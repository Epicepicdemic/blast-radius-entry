"""The pinned source extent of each multiline statement or compound header."""
import ast


def spans(tree):
    found = set()
    for node in ast.walk(tree):
        if not isinstance(node, ast.stmt):
            continue
        first, last = node.lineno, node.end_lineno
        body = getattr(node, "body", None)
        if isinstance(body, list) and body and isinstance(body[0], ast.stmt):
            # A suite is composed of its own statements. Using its first line
            # as the end of a header would join unrelated tests to the guard.
            first_child = body[0]
            decorators = getattr(first_child, "decorator_list", ())
            suite_start = min([first_child.lineno] + [d.lineno for d in decorators])
            last = max(first, suite_start - 1)
        if first < last:
            found.add((first, last))
    return sorted(found)


def closure_factories(trees):
    """Only a plain def that creates one closure and returns it untouched."""
    found = {}
    for path, tree in trees.items():
        future = any(isinstance(n, ast.ImportFrom) and n.module == "__future__" and
                     any(a.name == "annotations" for a in n.names) for n in tree.body)
        for node in tree.body:
            if not isinstance(node, ast.FunctionDef) or node.decorator_list or len(node.body) != 2:
                continue
            inner, ret = node.body
            if not (isinstance(inner, ast.FunctionDef) and not inner.decorator_list
                    and not inner.args.defaults and not any(inner.args.kw_defaults)
                    and not getattr(inner, "type_params", ())
                    and isinstance(ret, ast.Return) and isinstance(ret.value, ast.Name)
                    and ret.value.id == inner.name and inner.body[0].lineno > inner.lineno and future):
                continue
            if any(n is not node and (
                isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and n.name == node.name
                or isinstance(n, ast.Name) and n.id == node.name and isinstance(n.ctx, (ast.Store, ast.Del))
                or isinstance(n, ast.alias) and (n.asname or n.name) == node.name
            ) for n in ast.walk(tree)):
                continue
            name = path.removesuffix(".py").replace("/", ".").removesuffix(".__init__")
            found[name + "." + node.name] = [path, inner.body[0].lineno, inner.end_lineno]
    return found


def raw_namespace_lines(tree):
    parents = {child: node for node in ast.walk(tree) for child in ast.iter_child_nodes(node)}
    for node in ast.walk(tree):
        if isinstance(node, ast.Attribute) and node.attr == "__dict__":
            parent = parents[node]
            call = parents.get(parent)
            if (isinstance(parent, ast.Attribute) and parent.attr in ("get", "pop")
                    and isinstance(call, ast.Call) and call.args and isinstance(call.args[0], ast.Constant)):
                yield node.lineno, call.args[0].value
            elif (isinstance(parent, ast.Compare) and parent.comparators == [node]
                  and isinstance(parent.ops[0], (ast.In, ast.NotIn))):
                continue
            else:
                yield node.lineno, "*"
        elif (getattr(node, "id", None) in ("vars", "getattr_static", "getmembers_static")
              or getattr(node, "attr", None) in ("getattr_static", "getmembers_static", "__getattribute__")):
            yield node.lineno, "*"


def class_metadata(trees, lines):
    from collections import defaultdict
    raw = defaultdict(int)
    for path, tree in trees.items():
        for line, name in raw_namespace_lines(tree):
            raw[str(name)] |= lines[path].get(line, 0)
    base = next(n for n in trees["sqlglot/tokens.py"].body if isinstance(n, ast.ClassDef) and n.name == "_TokenizerBase")
    init = next(n for n in base.body if isinstance(n, ast.FunctionDef) and n.name == "__init_subclass__")
    names = {n.attr for n in ast.walk(init) if isinstance(n, ast.Attribute)}
    names.update(n.value for n in ast.walk(init) if isinstance(n, ast.Constant) and type(n.value) is str)
    return raw, sorted(names)
