"""Bound local module edits only after a successful collection/import witness."""
from functools import lru_cache
from pathlib import Path

from impact import Observations, family_path
from module_reads import module_bounded
from mutation_summaries import module_name
from patching import parsed_source
from snapshot_cone import outer_functions
from verify import fork_masks


@lru_cache(maxsize=1)
def observations():
    return Observations(Path(__file__).with_name("impact.bin"))


def candidate(index, changes, snapshot, equal):
    if len(changes) != 1:
        return None
    ch = changes[0]
    if not family_path(ch.path):
        return None
    users = index.bits("users", ch.path)
    if not users or users == index.all or ch.path in index.warm_unknown.get("users", ()):
        return None
    if not module_bounded(ch, equal, module_name(ch.path)):
        return None
    # The reads branch bounds namespace effects. Preserve the PB's separate obligations
    # for changed runtime functions and for aliases of shared writers.
    if snapshot is None:
        old, new = (outer_functions(parsed_source(s)) for s in (ch.before, ch.after))
        if old.keys() != new.keys() or any(not equal(fn, new[key]) for key, fn in old.items()):
            return None
    else:
        users |= snapshot[0] | snapshot[1]
    ix = observations()
    if ix.ids != index.ids:
        return None
    section = ix.section(ch.path)
    points = ch.removed | ch.insertions | {n+1 for n in ch.insertions}
    if section is None or points.intersection(section["order"]) or points.intersection(section["warm_unknown"]):
        return None
    mask = users | ix.family(ch.path) | index.import_users(ch.path)
    return mask if mask != index.all else None


def confirm(suite, changes, deadline):
    def check():
        # A clean cold import of the changed module, every test file, and the registered
        # dialects rejects broken bindings and collection failures before using the bound.
        import importlib
        try:
            fixtures, bypassed = suite._prepare_child(changes, None)
            importlib.import_module(module_name(changes[0].path))
            from sqlglot import Dialect
            list(Dialect.classes.values())
        except (ImportError, SyntaxError, NameError, AttributeError):
            return 0, 1
        return int(not fixtures.files and not bypassed()), 0
    return fork_masks(check, (0, 0), deadline, 2.5)
