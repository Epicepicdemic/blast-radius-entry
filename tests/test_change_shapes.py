import ast
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

from selector import Index
from table_readers import build
from test_line_b_switches import _diff_change, _mini_index


class ChangesTest(unittest.TestCase):
    path = 'sqlglot/example.py'

    def select(self, old, new, masks, **switches):
        with TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            change = _diff_change(root, self.path, old, new)
            data = _mini_index(self.path, ['t0', 't1', 't2', 't3'], line_masks=masks,
                               attr_masks={'__code__': 1})
            with patch.dict('os.environ', switches), patch('change_shapes.pinned_table_readers',
                                                           return_value={'TABLE': (6, 0)}):
                return Index(data, root=root).select(change)[0]

    def test_single_entry_only(self):
        for display in ('{"k": 1}', '[1]', '(1,)'):
            src = f'class C:\n    TABLE = {display}\n'
            self.assertEqual(self.select(src, src.replace('1', '2'), {}), 7)
            for replacement in ('factory()', 'MISSING', 'lambda a=effect(): a'):
                self.assertEqual(self.select(src, src.replace('1', replacement), {}), 15)
            self.assertEqual(self.select(src, src.replace('1', '2'), {}, CLASS_TABLE_ENTRIES='0'), 15)
        src = 'class C:\n    TABLE = {"a": 1, "b": 3}\n'
        self.assertEqual(self.select(src, src.replace('1', '2').replace('3', '4'), {}), 7)
        for new in (src.replace('"a"', '"c"'), src.replace('1', '2').replace('3','side()'),
                    src.replace('1', '2') + 'side_effect()\n'):
            self.assertEqual(self.select(src, new, {}), 15)

    def test_build_follows_copy_chains_and_inherited_lookups(self):
        src = ('class Parent:\n    TABLE = {"x": 1}\nclass Child(Parent):\n'
               '    COPY = {k:v for k,v in {**Parent.TABLE}.items() if k}\n'
               '    AGAIN = {**COPY}\nclass Grandchild(Child):\n    pass\n'
               'def read(c):\n    return c.TABLE, Grandchild.AGAIN\n')
        with TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            p = root / self.path
            p.parent.mkdir()
            p.write_text(src)
            data = _mini_index(self.path, list('abcd'), line_masks={4:15, 5:15, 9:4})
            self.assertEqual(int(build(root, data)['TABLE'][0], 16), 4)

    def test_inserted_branch_widens_to_entire_existing_function(self):
        src = 'def f(n):\n    if n < 1:\n        return 7\n    return n\n'
        dst = src.replace('    return n', '    if n == 4:\n        return 8\n    return n')
        self.assertEqual(self.select(src, dst, {2:2, 3:4, 4:2}), 7)
        self.assertEqual(self.select(src, dst, {2:2}, FUNCTION_INSERTIONS='0'), 15)
        for extra in ('    mystery(n)\n', '    class Nested: pass\n', '    def inner(): pass\n',
                      '    if UNBOUND: return 1\n', '    n.values.append(3)\n'):
            self.assertEqual(self.select(src, src.replace('    return n', extra+'    return n'), {2:2}), 15)
        self.assertEqual(self.select(src, src+'outside()\n', {2:2}), 15)

    def test_inserted_early_exit_cannot_bypass_unknown_side_effect(self):
        src = 'def f(n):\n    n.registry.clear()\n    return n\n'
        dst = src.replace('    n.registry', '    if not n: return 0\n    n.registry')
        self.assertEqual(self.select(src, dst, {2:2}), 15)

    def test_same_call_slot_and_fresh_string(self):
        from change_shapes import unchanged_call_arguments
        from selector import equal_trees
        from shared_writes import shared_write_effect
        src = 'def f(obj):\n    sink(obj, "old")\n'
        with TemporaryDirectory() as tmp:
            ch = _diff_change(Path(tmp).resolve(), self.path, src, src.replace('"old"', 'f"value={obj}"'))
            a,b = ast.parse(ch.before), ast.parse(ch.after)
            left,right = unchanged_call_arguments(a,b,ch,equal_trees)
            self.assertEqual({n.id for n in left}, {'obj'})
            self.assertFalse(shared_write_effect(b, ch.added, unchanged=right, fresh_literals=True)[0])
            self.assertTrue(shared_write_effect(b, ch.added, fresh_literals=True)[0])
            self.assertTrue(shared_write_effect(b, ch.added, unchanged=right)[0])
            for edit in ('other(obj, "new")', 'sink("new", obj)', 'sink(obj, *args)'):
                new = ast.parse(src.replace('sink(obj, "old")', edit))
                self.assertEqual(unchanged_call_arguments(a,new,ch,equal_trees), (set(), set()))
        src = 'STATE = {}\ndef run():\n    sink(STATE, 1)\n'
        tree = ast.parse(src)
        arg = tree.body[1].body[0].value.args[0]
        self.assertTrue(shared_write_effect(tree, {3}, unchanged={arg})[0])

    def test_local_scope_only(self):
        src = 'def f(x):\n    return x + 1\n'
        dst = 'def f(x):\n    y = x + 1\n    return y + 2\n'
        self.assertEqual(self.select(src, dst, {2:4}), 5)
        self.assertEqual(self.select(src, dst, {2:4}, LOCAL_SCOPE_CHANGES='0'), 15)
        for bad in ('    y = lambda: x\n    return y()', '    yield x', '    class Inner: pass\n    return x'):
            self.assertEqual(self.select(src, 'def f(x):\n'+bad+'\n', {2:4}), 15)
        src = 'y = 1\ndef f(x):\n    if x: return y\n    return x\n'
        dst = src.replace('    return x\n', '    y = 2\n    return x\n')
        self.assertEqual(self.select(src, dst, {3:4, 4:4}), 15)

    def test_unused_import_includes_external_reexport_consumers(self):
        data = {'eager':{}, 'exports':{}, 'from':{'sqlglot.example:chain':'4'}}
        with patch('change_shapes.pinned_imports', return_value=data):
            a='from itertools import chain\nx = 1\n'
            self.assertEqual(self.select(a,'x = 1\n',{}),5)
            reexport = '__all__ = ["chain"]\n'
            self.assertEqual(self.select(a+reexport,'x = 1\n'+reexport,{}),5)
            self.assertEqual(self.select(a,'x = 1\n',{},UNUSED_IMPORTS='0'),15)
            self.assertEqual(self.select(a+'def f(): return chain\n','x = 1\ndef f(): return chain\n',{}),15)
            for imp in ('from itertools import nonexistent', 'from opaque import action',
                        'from itertools import *','from __future__ import annotations'):
                self.assertEqual(self.select('x = 1\n',imp+'\nx = 1\n',{}),15)

    def test_fast_data_and_early_test_fallback(self):
        import json
        import marshal
        from pinned_data import load
        from patching import Change
        with TemporaryDirectory() as tmp:
            p=Path(tmp)/'facts.json'
            facts={'ids':['a'], 'lines':{'x':3}}
            p.write_text(json.dumps(facts))
            self.assertEqual(load(p,True),facts)
            p.with_suffix('.bin').write_bytes(marshal.dumps(facts))
            self.assertEqual(load(p,True),load(p,False))
        data=_mini_index('tests/test_a.py', ['a','b'], line_masks={2:1})
        changed=Change('tests/test_a.py', b'def test_a():\n    pass\n',
                       b'def test_a():\n    assert 0\n', {2}, set(), {2})
        with patch('selector.Project') as expensive:
            idx=Index(data,expensive)
            self.assertEqual(idx.select_changes([changed])[0],idx.all)
            expensive.patched.assert_not_called()

    def test_local_loop_index_preserves_original_iteration(self):
        a='def f(rows):\n    for row in rows:\n        consume(row)\n'
        b=a.replace('for row in rows:', 'for i, row in enumerate(rows):')
        self.assertEqual(self.select(a,b,{2:2,3:4}),7)
        self.assertEqual(self.select(a,b.replace('enumerate(rows)','reversed(rows)'),{2:2}),15)
        a=a.replace('f(rows)', 'f(rows, enumerate)')
        self.assertEqual(self.select(a,a.replace('for row in rows:', 'for i, row in enumerate(rows):'),{2:2}),15)

    def test_directive_follows_unchanged_bytes_only(self):
        src='def f(n):\n    return n\n\ndef g(x):\n    return x.a  # type: ignore[attr-defined]\n'
        dst=src.replace('    return n', '    if n is None: return 1\n    return n')
        self.assertEqual(self.select(src,dst,{2:2}),3)
        self.assertEqual(self.select(src,dst.replace('attr-defined','assignment'),{2:2}),15)
        moved=dst.replace('def g(x):\n    return x.a  # type: ignore[attr-defined]',
                          'def g(x):  # type: ignore[attr-defined]\n    return x.a')
        self.assertEqual(self.select(src,moved,{2:2}),15)

    def test_inserted_local_cannot_feed_a_surviving_shared_write(self):
        for use in ('STATE["flag"] = flag', 'cache.append(flag)', 'publish(flag)',
                    'alias = flag\n    publish(alias)', 'if flag:\n        side_effect()'):
            a='def f(flag):\n    '+use+'\n    return flag\n'
            b=a.replace('def f(flag):\n', 'def f(flag):\n    flag = True\n')
            self.assertEqual(self.select(a,b,{2:2,3:2}),15,use)
        a='def f(n):\n    from hooks import len\n    return 2\n'
        b=a.replace('    return 2', '    if len(n): return 1\n    return 2')
        self.assertEqual(self.select(a,b,{2:2,3:2}),15)

    def test_imported_module_attribute_requires_a_stable_definition(self):
        from mutation_summaries import Project, build as summaries
        src='import sqlglot.dep as dep\nclass C:\n    TABLE = {"x": dep.old}\n'
        dep='def old(): pass\ndef new(): pass\n'
        with TemporaryDirectory() as tmp:
            root=Path(tmp).resolve()
            project=Project(summaries([(self.path,src),('sqlglot/dep.py',dep)]))
            data=_mini_index(self.path,list('abcd'),line_masks={})
            data['imports']={self.path:['sqlglot/dep.py'], 'sqlglot/dep.py':[]}
            with patch('change_shapes.pinned_table_readers',return_value={'TABLE':(4,0)}):
                index=Index(data,project,root=root)
                good=_diff_change(root,self.path,src,src.replace('dep.old','dep.new'))
                self.assertEqual(index.select_changes([good])[0],4)
                bad=_diff_change(root,self.path,src,src.replace('dep.old','dep.missing'))
                self.assertEqual(index.select_changes([bad])[0],15)
                data['imports']['sqlglot/dep.py']=[self.path]
                self.assertEqual(index.select_changes([good])[0],15)

    def test_fresh_conditional_and_nested_arguments(self):
        from shared_writes import shared_write_effect
        for expr in ('not state', 'state is None', '1 if flag else f"{flag}"',
                     '[f"{state}", (1, 2)]'):
            tree=ast.parse('def f(state, flag):\n    opaque('+expr+')\n')
            self.assertFalse(shared_write_effect(tree,{2},fresh_literals=True)[0],expr)
        for expr in ('[] if flag else STATE', '[STATE]', 'f"{STATE.pop()}"'):
            tree=ast.parse('def f(flag):\n    opaque('+expr+')\n')
            self.assertTrue(shared_write_effect(tree,{2},fresh_literals=True)[0],expr)

    def test_on_demand_uses_every_edited_namespace(self):
        from mutation_summaries import Project, build
        from patching import Change
        src='from sqlglot.dep import use\ndef run(x):\n    use(x)\n'
        dep='def use(x):\n    return None\n'
        modified=dep.replace('return None', 'x.append(1)')
        base=Project(build([(self.path,src),('sqlglot/dep.py',dep)]))
        changes=[Change(self.path,src.encode(),src.encode(),{3},set(),{3}),
                 Change('sqlglot/dep.py',dep.encode(),modified.encode(),{2},set(),{2})]
        for lazy in (False,True):
            project=base.patched(changes,on_demand=lazy)
            tree=project.source('sqlglot.example').tree
            fn=tree.body[-1]
            call=fn.body[0].value
            self.assertEqual(project.arguments_at_risk('sqlglot.example',tree,fn,call),[(call.args[0],False)])

    def test_loop_exit_cannot_skip_writes_on_later_iterations(self):
        src='def f(rows):\n    for row in rows:\n        publish(row)\n        pass\n'
        dst=src.replace('        pass','        if row: return 3')
        self.assertEqual(self.select(src,dst,{2:2,3:4}),15)

    def test_local_condition_cannot_bypass_a_surviving_write(self):
        src = 'def f(flag):\n    if flag: return 1\n    publish(42)\n'
        dst = src.replace('    if flag:', '    flag = True\n    if flag:')
        self.assertEqual(self.select(src, dst, {2: 2}), 15)

    def test_loop_return_checks_iterator_and_else_effects(self):
        for src in ('def f():\n    while advance():\n        pass\n',
                    'def f(rows):\n    for row in rows:\n        pass\n    else:\n        publish(1)\n'):
            dst = src.replace('        pass', '        if True: return 2\n        pass')
            self.assertEqual(self.select(src, dst, {2: 2, 3: 4}), 15)

    def test_inserted_docstring_changes_definition_state(self):
        src = 'def f(x):\n    return x\n'
        dst = src.replace('    return', '    """New runtime docstring."""\n    return')
        self.assertEqual(self.select(src, dst, {2: 2}), 15)

    def test_removed_fromlist_does_not_skip_submodule_initialization(self):
        src = 'import registered\nfrom registered import plugin\nx = 1\n'
        dst = src.replace('from registered import plugin\n', '')
        data = {'eager': {}, 'exports': {}, 'from': {}}
        with patch('change_shapes.pinned_imports', return_value=data):
            self.assertEqual(self.select(src, dst, {3: 2}), 15)
