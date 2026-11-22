"""Run a small closed delayed-body cone in a bounded, fresh interpreter fork."""
import ast
import os
import sys
from time import monotonic


def eligible(ch):
    from patching import parsed_source
    if ch.path.startswith('tests/fixtures/') and ch.path.endswith('.json'):
        return True
    if not ch.path.startswith("sqlglot/") or not ch.path.endswith(".py") or not ch.removed or not ch.added:
        return False
    # Nested factories are created while importing many dialects. Their actual
    # call cone is often short enough to verify completely without warming the suite.
    pts=ch.removed
    if len(pts)>160:return False
    def nested(n):
        return isinstance(n,ast.FunctionDef) and n.lineno<min(pts) and max(pts)<=n.end_lineno
    for fn in parsed_source(ch.before).body:
        if nested(fn) and any(nested(n) for s in fn.body for n in ast.walk(s)):return True
    from cone import body_changes
    from selector import equal_trees
    changes=body_changes(ch,equal_trees)
    return bool(changes and len(changes)==1)


def check(selector,ch,mask,raw,durations,numbers,deadline):
    from verify import WarmSuite,fork_masks,runnable
    if raw is None or raw[4] or raw[1] or not 0<mask.bit_count()<=11:return None
    idx=[i for i in range(len(numbers)) if mask>>i&1]
    if any(numbers[i] is None or not runnable(selector.ix.ids[i]) for i in idx):return None
    if sum(durations[numbers[i]] for i in idx)>1450 or not eligible(ch):return None
    def body():
        os.chdir(selector.root)
        sys.path.insert(0,str(selector.root))
        suite=WarmSuite(selector.root,selector.ix.ids)
        passed,readers=suite.execute(selector.team,[ch],idx,set(raw[2]),None)
        return passed,readers
    passed,readers=fork_masks(body,(0,selector.ix.all),min(deadline,monotonic()+3.4),1.75)
    if readers:return None
    return mask&~passed


def fixture(selector, ch, mask, durations, numbers, deadline):
    """Replay short, direct readers under a strict file overlay and preserve every bypass."""
    if not ch.path.startswith('tests/fixtures/') or not ch.path.endswith('.json') or not 0<mask.bit_count()<=8:
        return None
    import json
    try:json.loads(ch.before);json.loads(ch.after)
    except (UnicodeError,ValueError):return None
    from verify import WarmSuite,runnable,fork_masks
    ids=[i for i in range(len(numbers)) if mask>>i&1]
    if any(numbers[i] is None or not runnable(selector.ix.ids[i]) for i in ids) or sum(durations[numbers[i]] for i in ids)>900:return None
    def run():
        os.chdir(selector.root);sys.path.insert(0,str(selector.root))
        suite=WarmSuite(selector.root,selector.ix.ids)
        return suite.execute(selector.team,[ch],ids,(),None)
    passed,readers=fork_masks(run,(0,selector.ix.all),min(deadline,monotonic()+2.2),1.3)
    return mask&~passed if not readers else None
