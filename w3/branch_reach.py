"""Compare bytecode along the recorded original control flow of a checked TPC-DS signature."""
import dis
import gzip
import hashlib
import json
import marshal
from functools import lru_cache
from pathlib import Path
import sys
import types


@lru_cache(maxsize=1)
def footprint():
    with gzip.open(Path(__file__).with_name("branches.json.gz")) as f:
        data = json.load(f)
    return data["paths"] if data["python"] == list(sys.version_info[:3]) else {}


def code_names(root):
    by_name = {}
    def collect(co):
        if co.co_qualname in by_name:
            by_name[co.co_qualname] = None
        else:
            by_name[co.co_qualname] = co
        for child in co.co_consts:
            if isinstance(child, types.CodeType):
                collect(child)
    collect(root)
    return by_name


def matching_path(old, new, single):
    # Confine this proof to ordinary, synchronous functions. Exception-table edges
    # and children whose code objects escape would require additional successors.
    if old.co_exceptiontable or new.co_exceptiontable or old.co_flags & (0x20 | 0x80 | 0x200):
        return False
    if any(isinstance(c, types.CodeType) for c in (*old.co_consts, *new.co_consts)):
        return False
    for name in ("co_qualname", "co_flags", "co_varnames", "co_argcount", "co_posonlyargcount",
                 "co_kwonlyargcount", "co_cellvars", "co_freevars", "co_names"):
        if getattr(old, name) != getattr(new, name):
            return False
    if old.co_consts[:1] != new.co_consts[:1]:
        return False
    def decode(code):
        seq = list(dis.get_instructions(code))
        return {ins.offset: (ins, seq[i+1].offset if i+1 < len(seq) else None)
                for i, ins in enumerate(seq)}
    left, right = decode(old), decode(new)
    todo, seen = [(0,0)], set()
    while todo:
        pos, target = todo.pop()
        if (pos, target) in seen:
            continue
        seen.add((pos,target))
        if pos not in left or target not in right:
            return False
        a, after = left[pos]
        b, following = right[target]
        if a.opname != b.opname:
            return False
        if a.opcode in dis.hasjump:
            if a.argval not in left or b.argval not in right:
                return False
            if after == a.argval:
                return False
            if a.opname in ("JUMP_FORWARD", "JUMP_BACKWARD", "JUMP_BACKWARD_NO_INTERRUPT"):
                todo.append((a.argval,b.argval))
                continue
            # Accept a one-sided edge only for ordinary two-way boolean/None jumps
            # with a witnessed destination matching this original disassembly.
            dest = single.get(str(pos)) if a.opname.startswith("POP_JUMP_IF_") else None
            if dest != after:
                todo.append((a.argval,b.argval))
            if dest == a.argval:
                continue
        else:
            if a.arg != b.arg:
                return False
            if a.opcode in dis.hasconst and marshal.dumps(a.argval, 2) != marshal.dumps(b.argval, 2):
                return False
            if a.opname in ("RETURN_VALUE", "RETURN_CONST", "RAISE_VARARGS", "RERAISE"):
                continue
        if after is None or following is None:
            return False
        todo.append((after,following))
    return True


def same_signature(ch, hot):
    from heavy_reach import same_header
    from impact import functions
    from patching import compiled_source
    from proofs import baseline_code, scope_changed
    observations = footprint().get(ch.path)
    if not observations or not hot or any(p != ch.path for p, *_ in hot):
        return False
    old_tree, new_tree = functions(ch.before), functions(ch.after)
    original, modified = baseline_code(ch.before,ch.path), compiled_source(ch.after,ch.path)
    if scope_changed(original,modified):
        return False
    before, after = code_names(original), code_names(modified)
    for _,name,_,_ in hot:
        a,b = before.get(name), after.get(name)
        if a is None or b is None or old_tree.get(name) is None or new_tree.get(name) is None:
            return False
        if not same_header(old_tree[name],new_tree[name]):
            return False
        rec = observations.get(f"{name}:{a.co_firstlineno}")
        if not rec or rec[0] != hashlib.sha256(a.co_code).hexdigest() or not matching_path(a,b,rec[1]):
            return False
    return True
