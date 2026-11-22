"""Find the first statement at which two ordinary function bodies can differ."""
import ast
from functools import lru_cache

from impact import functions, physical_lines
from patching import compiled_source, parsed_source

FN = (ast.FunctionDef, ast.AsyncFunctionDef)
SUITES = {"body", "orelse", "finalbody"}
END_NODES = (ast.If, ast.For, ast.While, ast.Try, ast.With, ast.Match)


def same(a, b):
    if isinstance(a, ast.AST):
        return type(a) is type(b) and all(same(getattr(a, k), getattr(b, k)) for k in a._fields)
    if isinstance(a, list):
        return isinstance(b, list) and len(a) == len(b) and all(same(x, y) for x, y in zip(a, b))
    return type(a) is type(b) and a == b


def local_kinds(fn):
    # A new assignment can shadow an earlier global read anywhere in this scope.
    # New local names with no original reads cannot change an unchanged expression.
    stores, reads = set(), set()
    for n in ast.walk(fn):
        if isinstance(n, (ast.Global, ast.Nonlocal)):
            return None
        if isinstance(n, ast.Name):
            (reads if isinstance(n.ctx, ast.Load) else stores).add(n.id)
        elif isinstance(n, ast.ExceptHandler) and n.name:
            stores.add(n.name)
        elif isinstance(n, ast.alias):
            stores.add(n.asname or n.name.partition(".")[0])
    return stores, reads


def frontier(old, new):
    """Return old regions dominating every changed statement on the matched syntax."""
    regions = []
    def add(n):
        regions.append((n.lineno, n.end_lineno))
    def compare(a, b):
        if same(a, b):
            return
        if type(a) is not type(b) or not isinstance(a, END_NODES):
            if not line_anchor(a) and not (isinstance(a,ast.Expr) and isinstance(a.value,ast.Call)):
                add(old)
            else:add(a)
            return
        if not all(same(getattr(a, k), getattr(b, k)) for k in a._fields if k not in SUITES):
            add(a)
            return
        for k in a._fields:
            if k in SUITES:
                suite(getattr(a, k), getattr(b, k), a)
    def suite(left, right, parent):
        # Unchanged prefix and suffix delimit insertions inside a statement list.
        i = 0
        while i < min(len(left), len(right)) and same(left[i], right[i]):
            i += 1
        end_old, end_new = len(left), len(right)
        while end_old > i and end_new > i and same(left[end_old-1], right[end_new-1]):
            end_old -= 1
            end_new -= 1
        if end_old == i and end_new == i:
            return
        if end_old-i == end_new-i:
            for a, b in zip(left[i:end_old], right[i:end_new]):
                compare(a, b)
        elif i < len(left) and line_anchor(left[i]):
            # Any execution of the differing interval must reach its first old
            # statement; include all removed statements as additional anchors.
            for n in left[i:max(i+1,end_old)]:
                add(n)
        else:
            add(parent)
    suite(old.body, new.body, old)
    return regions


def line_anchor(n):
    # Avoid optimized-away expressions, including literals, asserts and pass.
    if isinstance(n,ast.Expr) and isinstance(n.value,ast.Call):return True
    return isinstance(n,(ast.Assign,ast.AnnAssign,ast.AugAssign,ast.Return,ast.Raise,ast.For,ast.While,ast.If)) and not (
            isinstance(n,ast.AnnAssign) and n.value is None or
            isinstance(n,(ast.If,ast.While)) and isinstance(n.test,ast.Constant))


def digests(fn):
    return tuple(ast.dump(getattr(fn, k)) if isinstance(getattr(fn, k),ast.AST) else
                 [ast.dump(n) for n in getattr(fn,k)] if isinstance(getattr(fn,k),list) else getattr(fn,k)
                 for k in fn._fields if k!="body")


def body_info(ix,ch):
    """Keep only delayed bodies with byte-identical surroundings and inert headers."""
    import textwrap
    section=ix.section(ch.path)
    if not section or "functions" not in section or not ch.removed and not ch.insertions:
        return None
    left,right=physical_lines(ch.before),physical_lines(ch.after)
    shift=len(right)-len(left)
    for name,(start,body,end,ptr) in section["functions"].items():
        if not all(body<=n<=end for n in ch.removed) or not all(body-1<=n<=end for n in ch.insertions):
            continue
        if not all(body<=n<=end+shift for n in ch.added):
            continue
        if left[:start-1]!=right[:start-1] or left[end:]!=right[end+shift:]:
            continue
        def parse(lines,end):
            code=textwrap.dedent("\n".join(lines[start-1:end]))
            nodes=ast.parse(code,type_comments=True).body
            return nodes[0] if len(nodes)==1 and isinstance(nodes[0],FN) else None
        a,b=parse(left,end),parse(right,end+shift)
        if not a or not b or digests(a)!=digests(b) or ast.get_docstring(a,clean=False)!=ast.get_docstring(b,clean=False):
            continue
        if any(not isinstance(d,ast.Name) or d.id not in ("property","classmethod","staticmethod") for d in a.decorator_list+b.decorator_list):
            continue
        # Compile the entire postimage. A function fragment alone cannot certify
        # indentation, enclosing scopes or compilation of a changed module.
        compiled_source(ch.after,ch.path)
        ranges=frontier(a,b)
        if not ranges:
            continue
        kinds_a,kinds_b=local_kinds(a),local_kinds(b)
        if not kinds_a or not kinds_b:
            return None
        # Fall back to callable coverage for closures, changed binding modes, and
        # instructions without a source-line event. Include cold/fixture contexts.
        wide=bool((kinds_a[0]^kinds_b[0]) & (kinds_a[1] & kinds_b[1]))
        import types
        def signature(fn):
            # A different lexical binding can alter an unedited read. New private
            # locals are harmless only if the old program never read their name.
            tree=ast.Module(body=[fn],type_ignores=[])
            code=next(x for x in compile(tree,"<scope>","exec",dont_inherit=True).co_consts
                      if isinstance(x,types.CodeType))
            return (code.co_cellvars,code.co_freevars,code.co_flags)
        wide |= signature(a)!=signature(b)
        if any(isinstance(n, (ast.Nonlocal,ast.Global,ast.ClassDef,ast.FunctionDef,ast.AsyncFunctionDef))
               for fn in (a,b) for stmt in fn.body for n in ast.walk(stmt)):
            wide=True
        points=set()
        for l,r in ranges:
            points.update(range(start+l-1,start+r))
        if points.intersection(section["order"]) or points.intersection(section["warm_unknown"]):
            return None
        from impact import disjoint_ranges
        called=ix.bits(ptr)|disjoint_ranges(section,[(body,end)],ix)
        cap=called if wide else disjoint_ranges(section,[(n,n) for n in points],ix)
        from bounds import pool_facts
        workers=pool_facts()
        if wide:worker_lines=range(body,end+1)
        else:worker_lines=points
        per_line=workers["lines"].get(ch.path,{})
        for line in worker_lines:cap |= per_line.get(line,0)
        cap |= (workers["unproved"] & called)
        # A non-empty function that is absent from both independent profiles
        # provides no positive call receipt for this proof.
        if called:
            return name,called,cap,a,b,start,body,end
    return None
