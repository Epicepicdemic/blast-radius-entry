"""Profile value-sensitive expression schema reads, including derived required-key validation."""
import ast
from collections import defaultdict
import json
import os
from pathlib import Path
import sys

import metadata_profile as base

key_only = set()
validation = set()
risk = defaultdict(set)

LOOP = """for k in self.required_args:
    v = self.args.get(k)
    if v is None or (isinstance(v, list) and not v):
        if errors is None:
            errors = []
        errors.append(f"Required keyword: '{k}' missing for {self.__class__}")
"""

def site_map():
    template=ast.dump(ast.parse(LOOP).body[0])
    for folder in ("sqlglot","tests"):
        for path in (base.root/folder).rglob("*.py"):
            tree=ast.parse(path.read_bytes())
            parents={c:p for p in ast.walk(tree) for c in ast.iter_child_nodes(p)}
            uses=defaultdict(list)
            for n in ast.walk(tree):
                if isinstance(n,ast.For) and ast.dump(n)==template:
                    validation.add((str(path),n.iter.lineno))
                if not isinstance(n,ast.Attribute) or n.attr!="arg_types":
                    continue
                p=parents.get(n)
                pure=(isinstance(p,ast.Compare) and len(p.ops)==1 and isinstance(p.ops[0],(ast.In,ast.NotIn))
                      and p.comparators[0] is n) or (isinstance(p,(ast.For,ast.comprehension)) and p.iter is n)
                uses[n.lineno].append(pure)
            key_only.update((str(path),line) for line,pure in uses.items() if all(pure))

def observe(obj,name,frame):
    if name not in base.FIELDS and name!="__dict__":
        return
    declaring=base.owner(obj)
    if declaring is None:return
    site=(frame.f_code.co_filename,frame.f_lineno)
    if name=="arg_types" and frame.f_code.co_qualname=="Expr.__init_subclass__" and site[0]==str(base.root/"sqlglot/expressions/core.py") and site[1] in base.derivation:
        return
    # Only direct reads rewritten by attr() may qualify as key-only operations.
    direct=sys._getframe(1).f_code is base.attr.__code__
    if direct and name=="arg_types" and site in key_only:return
    if direct and name=="required_args" and site in validation and type(obj.args) is dict:
        invalid = {k for k in obj.arg_types if obj.args.get(k) is None or
                   (isinstance(obj.args[k],list) and not obj.args[k])}
        if obj.required_args.isdisjoint(invalid):
            for key in invalid:
                risk[declaring,key].add(base.current)
            return
    risk[declaring,None].add(base.current)

def pytest_configure(config):
    site_map()
    base.observe=observe
    base.pytest_configure(config)

pytest_runtest_call=base.pytest_runtest_call
incomplete=set()
def pytest_runtest_logreport(report):
    base.pytest_runtest_logreport(report)
    if report.failed or report.skipped:
        incomplete.add(report.nodeid)

def pytest_sessionfinish(session,exitstatus):
    if os.getpid()!=base.pid:return
    out=dict(passed=sorted(base.passed-incomplete), incomplete=sorted(incomplete), rows=[[owner,key,sorted(ns)] for (owner,key),ns in risk.items()])
    Path(os.environ["SCHEMA_OUT"]).write_text(json.dumps(out,separators=(",",":")))
