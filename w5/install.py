"""Install supplemental pin proofs without changing the submission CLI."""
from pathlib import Path
import shutil
import subprocess
import sys

src=Path(__file__).parent
app=Path("/app")
for p in src.glob("*.py"):
    if p.name not in ("install.py","link.py"):
        shutil.copyfile(p,app/p.name)
def edit(name,old,new):
    p=app/name
    source=p.read_text()
    assert source.count(old)==1, (name,old)
    p.write_text(source.replace(old,new))
# Both shared-write analyses must use the same postimage name census.
p = app / "read_effects.py"
source = p.read_text()
start = source.index("    def missing(n):", source.index("def missing_call("))
end = source.index("    def compulsory(n):", start)
p.write_text(source[:start] + "    from binding_guards5 import unbound\n    def missing(n):\n        return unbound(n,scope,census)\n" + source[end:])
edit("shared_writes.py", "        if isinstance(node, (ast.Assign, ast.Delete)):\n            if any(shared_target", """        if isinstance(node, ast.ClassDef) and (node.bases or node.keywords or node.decorator_list):
            headers=[*node.bases,*node.keywords,*node.decorator_list]
            if overlaps(points, node.lineno, max([node.lineno]+[h.end_lineno for h in headers])) or any(overlaps(points,d.lineno,d.end_lineno) for d in node.decorator_list):
                return True
        if isinstance(node, (ast.Assign, ast.Delete)):
            if any(shared_target""")
edit("read_effects.py", "        if isinstance(n,ast.Call):return compulsory(n.func) or any(compulsory(a) for a in n.args) or any(compulsory(k.value) for k in n.keywords)", """        # Unknown nested calls can run code while argument expressions are evaluated.
        # A missing-name certificate applies to a direct lookup in this call only.
        if isinstance(n,ast.Call):return False""")
edit("shared_writes.py", "            callee = qualified_name(fn)", """            from registration5 import metaclass_call
            from binding_guards5 import new_callable
            if metaclass_call(node) or new_callable(node,scope,census):
                return True
            callee = qualified_name(fn)""")
edit("fast_select.py", "            changes = read_patch(path, root)", """            changes = read_patch(path, root)
            from registration5 import registration_bound
            registration = registration_bound(ix,changes)
            if registration is not None:
                limit, reason = registration
                return (limit,False,reason,True,0),limit""")
edit("fast_select.py", "        changes=read_patch(path,self.root) if changes is None else changes", """        changes=read_patch(path,self.root) if changes is None else changes
        from registration5 import registration_bound
        registration = registration_bound(ix,changes)
        if registration is not None:
            limit, reason = registration
            return limit,False,reason,True,0""")
edit("fast_select.py", "        independent=len(changes)==1", """        from registration5 import registration_bound
        registration = registration_bound(ix,changes)
        if registration is not None:
            limit, reason = registration
            return limit,False,reason,None
        independent=len(changes)==1""")
edit("fast_select.py","            owed=stress_obligation(ix,changes)",'''            if len(changes)==1:
                from rules5 import early
                proof=early(ix,changes[0])
                if proof is not None:
                    limit,reason=proof
                    return (limit,False,reason,True,0),limit
            owed=stress_obligation(ix,changes)''')
edit("shared_writes.py","                            classified = _classify_arg(arg, scope, comp_vars)", """                            from effects5 import predicate
                            if predicate(arg,scope,node,census):
                                continue
                            classified = _classify_arg(arg, scope, comp_vars)""")
edit("fast_select.py","        selected,protected,watch,hot,writers=analyze(self.team,changes,equal_trees,self.shared)","        from effects5 import configure\n        configure(changes)\n        selected,protected,watch,hot,writers=analyze(self.team,changes,equal_trees,self.shared)")
edit("shared_writes.py","            return not private(target.value, scope, cls)", """            from effects5 import owned_store,observed_shell
            from surgery5 import ctor_shell
            return not (private(target.value,scope,cls) or owned_store(target.value,scope,cls,census,tree) or
                        observed_shell(target.value,scope,census) or ctor_shell(target.value,scope,census))""")
edit("shared_writes.py","                if not private(fn.value, scope, cls):","""                from effects5 import owned_store,observed_shell
                from surgery5 import ctor_shell
                if not (private(fn.value,scope,cls) or owned_store(fn.value,scope,cls,census,tree) or
                        observed_shell(fn.value,scope,census) or ctor_shell(fn.value,scope,census)):""")
edit("shared_writes.py","                            if predicate(arg,scope,node,census):","""                            from surgery5 import immutable_result,unreachable
                            if node in unreachable(scope,census) or predicate(arg,scope,node,census) or immutable_result(arg,scope,node,census):""")
edit("ownership_effects.py", "    def read(target,seen=frozenset(),inner=False):", """    from alias_roots5 import identity, sources
    alias_sources = sources(fn)
    def read(target,seen=frozenset(),inner=False):
        key = identity(target)
        if key in alias_sources and key not in seen:
            readers = shared.get(key[1], 0)
            for origin in alias_sources[key]:
                if origin is None:
                    return None
                rooted = read(origin, seen | {key}, True)
                if rooted is None:
                    return None
                readers |= rooted
            if readers:
                return readers
        elif key is not None and key in seen:
            return None""")
edit("ownership_effects.py","        if not inner and shell(target,vals,allowed,methods):","""        from effects5 import nested_shell
        if not inner and isinstance(target,ast.Subscript) and nested_shell(target,fn,parsed_source(ch.before)):return 0
        if not inner and shell(target,vals,allowed,methods):""")
edit("verify.py","        # A removed mutation is invisible in the patched child's final state.", """        from pair5 import run as paired_run
        if hot:
            return paired_run(self,index,changes,indices,hot,writers,deadline,cap)
        # A removed mutation is invisible in the patched child's final state.""")
edit("bounds.py", "    return root_readers|timing_obligation(ix,a,b)", "    from resource5 import obligation\n    return root_readers|obligation(ix,ch,info,root_readers)")
edit("frontier.py", "def body_info(ix,ch):", """def body_info(ix,ch):
    k=id(ix)
    saved=getattr(ch,'_body_info5',None)
    if saved and saved[0]==k:
        return saved[1]
    value=_body_info(ix,ch)
    ch._body_info5=(k,value)
    return value

def _body_info(ix,ch):""")
edit("frontier.py","    regions = []","    from front5 import local_assignments\n    old,new=local_assignments(old),local_assignments(new)\n    regions = []")
edit('fast_select.py', '        def price(path):\n            mask, rev, why = choices[path]', """        checks_done={}
        def price(path):
            mask, rev, why = choices[path]
            key=(path,mask,rev)
            if not mandatory[path] and 0<mask.bit_count()<=11 and key not in checks_done:
                changes=read_patch(path,root)
                verified=None
                if len(changes)==1:
                    from short5 import check,fixture
                    ch=changes[0]
                    if mask.bit_count()<=8 and ch.path.startswith('tests/fixtures/') and ch.path.endswith('.json'):
                        selector.load_team()
                        verified=fixture(selector,ch,mask,durations,numbers,deadline)
                        label='complete fixture reader verification'
                    elif path in analyzed and not analyzed[path][1] and not analyzed[path][4]:
                        selector.load_team()
                        verified=check(selector,ch,mask,analyzed[path],durations,numbers,deadline)
                        label='complete short callback verification'
                    if verified is not None:
                        checks_done[path,verified,rev]=(verified,label)
                        checks_done[key]=(verified,label)
                checks_done.setdefault(key,None)
            if checks_done.get(key) is not None:
                mask,why=checks_done[key]
                choices[path]=mask,rev,why""")
edit("ownership_effects.py","        if isinstance(target,ast.Name):\n            if target.id in seen:return 0","""        if not inner:
            from effects5 import active,observed_shell
            from frontier import same
            from surgery5 import ctor_shell
            from selector import load_index
            from rules5 import resolver_for
            if active and active[0]==ch.path:
                original=active[2] if same(fn,active[2]) else active[3] if same(fn,active[3]) else None
                if original:
                    resolver=resolver_for(ch.path,ch.before if original is active[2] else ch.after)
                    actual=next((f for f,n in resolver.quals.items() if n==name),None)
                    if actual and (observed_shell(target,actual,resolver) or ctor_shell(target,actual,resolver)):return 0
        if isinstance(target,ast.Name):
            if target.id in seen:return 0""")
edit("verify.py","        if err and issubclass(err[0], AssertionError) and self.fixtures.files.keys() <= self.fixtures.seen:","""        synchronous=False
        if err and type(err[1]) in (NameError,UnboundLocalError,AttributeError,KeyError,IndexError,TypeError,ValueError):
            tb=err[2]
            body=getattr(test,test._testMethodName,None)
            code=getattr(body,'__code__',None)
            while tb is not None:
                if tb.tb_frame.f_code is code:synchronous=True;break
                tb=tb.tb_next
        if err and (issubclass(err[0],AssertionError) or synchronous) and self.fixtures.files.keys() <= self.fixtures.seen:""")
edit("pricing.py", "    return best\n", "    from packing5 import improve\n    return improve(best,required,ranked,durations)\n")
edit("economics.py","if total > 1500 or 2 * (minimum + total + 100 * writers.bit_count()) >= 5000:","if total>3750 or writers.bit_count()>12 or 2*(minimum+total+120*writers.bit_count())>10000:")
edit("selector.py","        remaining_cpu = cap - static_cpu\n        extra = index.all if writers else 0", """        writer_cap=10.0 if writers and hot else cap
        remaining_cpu = writer_cap - static_cpu
        extra = index.all if writers else 0""")
edit("selector.py","            subset = sorted(schedule(order, duration, min(1500, int(cap * 300))))", """            if writers and hot:
                subset=[i for i in order if writers & (1<<i)]
            else:
                subset=sorted(schedule(order,duration,min(1500,int(cap*300))))""")
edit("selector.py","< 1000 * cap", "< 1000 * writer_cap")
edit("fast_select.py","seconds=min(seconds,6.0)","seconds=min(seconds,10.5)")
edit('frontier.py','        kinds_a,kinds_b=local_kinds(a),local_kinds(b)','''        from nested5 import closure_ranges
        local_ranges=closure_ranges(a,b)
        kinds_a,kinds_b=local_kinds(a),local_kinds(b)
        if local_ranges and (not kinds_a or not kinds_b):
            # The complete outer code was compiled and its closure cells matched.
            kinds_a=kinds_b=(set(),set())''')
edit('frontier.py','        points=set()', '        if local_ranges:\n            ranges=local_ranges\n            wide=False\n        points=set()')
edit("frontier.py","            return name,called,cap,a,b,start,body,end","            from slice5 import refine\n            return refine(ix,ch,(name,called,cap,a,b,start,body,end))")
edit("witness.py","if cap.bit_count()>8:return None","if cap.bit_count()>12:return None")
edit("economics.py","from verify import runnable","from pair5 import writer_runnable as runnable")
edit("selector.py","            if writers:\n                order.sort(key=lambda i: not writers & (1 << i))", """            if writers and hot:
                from pair5 import writer_runnable
                order=[i for i in ordered if writers & (1<<i) and writer_runnable(index.ids[i])]
            elif writers:
                order.sort(key=lambda i: not writers & (1 << i))""")
edit('fixture_overlay.py','            if not change.path.endswith(".sql"):',
     '            if not (change.path.endswith(".sql") or change.path.startswith("tests/fixtures/") and change.path.endswith(".json")):')
edit('verify.py', '        fixtures.install()',
     """        # Every data file in the requested changes must actually be supplied.
        if any(c.path.startswith('tests/fixtures/') and not c.path.endswith('.py')
               and str(self.root/c.path) not in fixtures.files for c in changes):
            raise ValueError('unrepresented fixture postimage')
        fixtures.install()""")
edit('fast_select.py','                    if seconds<0.4:continue', """                    if seconds<0.4:continue
                    from viability5 import decline
                    if (not raw or not raw[4]) and decline(ix,read_patch(path,root),len(required[path])==len(all_numbers),len(required[path])<=64):
                        continue""")
# These two static analysis modules run only on parsed Python syntax.
for name in ('shared_writes.py', 'mutation_summaries.py'):
    edit(name, 'import ast\n', 'import syntax5 as ast\n')
edit('frontier.py','def same(a, b):\n', 'def same(a, b):\n    if a is b and isinstance(a,(ast.AST,list)):\n        return True\n')
edit('patching.py','@lru_cache(maxsize=2)\ndef parsed_source','@lru_cache(maxsize=4)\ndef parsed_source')
edit('patching.py','@lru_cache(maxsize=1)\ndef compiled_source','@lru_cache(maxsize=4)\ndef compiled_source')
edit('patching.py','        return apply_patch(stream.read(MAX_PATCH_BYTES + 1), root)',
     '        return _read_changes(stream.read(MAX_PATCH_BYTES + 1), root)\n\n\n@lru_cache(maxsize=4)\ndef _read_changes(raw, root):\n    return apply_patch(raw, root)')
edit('cone.py','def body_changes(change, equal):', """def body_changes(change, equal):
    # Both images are immutable here. The underlying comparison restores any
    # temporarily masked body before returning.
    key = (equal, HEADER_EDITS, HEADER_EXCLUDED_PATHS)
    memo = getattr(change, '_matched_bodies5', None)
    if memo is None or memo[0] != key:
        memo = (key, _body_changes(change, equal))
        change._matched_bodies5 = memo
    return memo[1]


def _body_changes(change, equal):""")
edit('shared_writes.py','def bindings(tree):','@lru_cache(maxsize=16)\ndef bindings(tree):')
subprocess.run([sys.executable,str(src/"link.py")],check=True)
shutil.copyfile(app/"wave3_entry.py",app/"wave5_entry.py")
