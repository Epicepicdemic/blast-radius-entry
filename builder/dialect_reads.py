"""Observe normal Python lookup without replacing the values stored by SQLGlot."""
import ast
import dis
from functools import cache
import sys

import probe


@cache
def raw_sites(filename):
    # A mappingproxy.get(literal, ...) exposes just that key. An escaped
    # mappingproxy can expose every value. Keep the latter as a wildcard.
    path = probe.source(filename)
    if not path:
        return {}
    with open(filename, "rb") as source:
        tree = ast.parse(source.read())
    result = {}
    for node in ast.walk(tree):
        if (isinstance(node, ast.Call) and isinstance(node.func, ast.Attribute)
                and node.func.attr == "get" and node.args
                and isinstance(node.args[0], ast.Constant) and type(node.args[0].value) is str):
            obj = node.func.value
            if isinstance(obj, ast.Attribute) and obj.attr == "__dict__":
                result[(obj.lineno, obj.end_lineno, obj.col_offset, obj.end_col_offset)] = node.args[0].value
    return result


@cache
def narrow_raw(code, offset):
    for instruction in dis.get_instructions(code):
        if instruction.offset == offset and instruction.opname == "LOAD_ATTR" and instruction.argval == "__dict__":
            return raw_sites(code.co_filename).get(tuple(instruction.positions), "*")
    return "*"


def install(module):
    dialect = module.Dialect
    meta = type(dialect)
    def wrap(original, on_class):
        def read(obj, name):
            value = original(obj, name)
            if name == "__dict__" and on_class:
                frame = sys._getframe(1)
                name = narrow_raw(frame.f_code, frame.f_lasti)
            if name == "*" or name.isupper():
                probe.read_names[probe.context].add(name)
            return value
        return read
    meta.__getattribute__ = wrap(meta.__getattribute__, True)
    dialect.__getattribute__ = wrap(dialect.__getattribute__, False)
