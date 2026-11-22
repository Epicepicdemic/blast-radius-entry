"""Price a conservative regional plan first. Refine uncertainty within the batch CPU allowance."""
import json
import marshal
import os
import sys
from time import monotonic, process_time

from bounded_batch import BATCH_SECONDS, bounded_results
from impact import Observations, classify, physical_lines
from patching import read_patch
from pricing import allocate
from regions import fallback
from value_bounds import schema_readers


class Selector:
    def __init__(self,root,app):
        self.root=root
        self.app=app
        self.ix=Observations(app/"impact.bin")
        self.team=None

    def load_team(self):
        if self.team is not None:
            return
        from selector import load_index
        index=load_index(self.root)
        if index.ids!=self.ix.ids:
            raise ValueError("pin inventories disagree")
        self.team=self.ix.team=index
        shared=self.app/"shared.bin"
        self.shared=marshal.loads(shared.read_bytes()) if shared.is_file() else None
        pool=set(json.loads((self.app/"pool_readers.json").read_bytes()))
        self.pool=sum(1<<i for i,n in enumerate(index.ids) if n in pool)

    def draft(self,path,changes=None):
        from hashlib import sha256
        from regions import changed_declaration
        from value_bounds import compare_site
        ix=self.ix
        changes=read_patch(path,self.root) if changes is None else changes
        combined=0
        reason=""
        weight=0
        provisional=False
        if len(changes)>1 and any(not c.path.startswith("tests/fixtures/") or not c.path.endswith(".sql") for c in changes):
            return ix.all,True,"combined change",False,sum(len(c.before) for c in changes)
        for ch in changes:
            section=ix.section(ch.path)
            if section is None or sha256(ch.before).digest()!=section["digest"]:
                return ix.all,True,"unindexed source",False,sys.maxsize
            if ch.path.startswith("tests/fixtures/") and ch.path.endswith(".sql"):
                b=classify(ix,ch)
                if not b:return ix.all,True,"unresolved fixture",True,0
                combined|=b[1]|b[2]
                reason=b[3]
                continue
            weight+=len(ch.before)*(1+len(ch.added)+len(ch.removed))
            if not (ch.path.startswith("sqlglot/") and ch.path.endswith(".py")):
                return ix.all,True,"outside code index",False,weight
            points=ch.removed|ch.insertions|{i+1 for i in ch.insertions}
            if points.intersection(section["order"]) or points.intersection(section["warm_unknown"]):
                return ix.all,True,"uncertain trace points",False,weight
            left,right=physical_lines(ch.before),physical_lines(ch.after)
            if section.get("owned_copy"):
                from ownership import unchanged_copy
                scope = unchanged_copy(section, ch, left, right)
                if scope is not None:
                    combined |= ix.reflect(ch.path, scope) | ix.hit(section, "opens")
                    reason = "copy flag on a witnessed detached or scalar operand"
                    continue
            if section.get("domains"):
                site=compare_site(ix,section,ch,left,right)
                if site is not None:
                    possible,scope=site
                    if not possible:
                        combined |= ix.reflect(ch.path,scope)|ix.hit(section,"opens")
                        reason="unchanged comparison on pin operands"
                        continue
            if ch.path.startswith("sqlglot/expressions/") and ix.meta.get("has_schema"):
                member=changed_declaration(ch,section,left,right)
                if member and member[0].endswith(".arg_types"):
                    self.load_team()
                    mask=schema_readers(ix,ch,*member[:3])
                    if mask is not None:
                        combined|=mask
                        reason="expression schema value readers"
                        continue
            # Boundaries and syntax are rechecked by the full selector for multi-file edits.
            row=fallback(ix,ch,section,left,right) if len(changes)==1 else None
            if row:
                mask,provisional,reason=row
                combined|=mask
                if not provisional:continue
            else:
                combined=ix.all
                reason="full pending syntax analysis"
                provisional=True
        return combined,provisional,reason,not provisional,weight

    def select(self, path):
        try:
            return self._refine(path)
        except SyntaxError:
            return self.ix.all, True, "invalid Python postimage", None

    def _refine(self,path):
        from cone import analyze,serialization_edit
        from selector import equal_trees
        self.load_team()
        changes=read_patch(path,self.root)
        ix=self.ix
        independent=len(changes)==1 or all(c.path.startswith("tests/fixtures/") and c.path.endswith(".sql") for c in changes)
        bounds=[classify(ix,c) for c in changes] if independent else []
        if bounds and all(b and b[0]=="direct" for b in bounds):
            keep=0
            for _,mask,owed,_ in bounds:keep|=mask|owed
            return keep,False,bounds[0][3],None
        bound=bounds[0] if len(bounds)==1 else None
        began = process_time()
        selected,protected,watch,hot,writers=analyze(self.team,changes,equal_trees,self.shared)
        if selected and any(serialization_edit(c) for c in changes):
            selected|=self.pool
            protected|=self.pool
        raw = (selected, protected, watch, hot, writers, process_time()-began)
        if writers:
            return ix.all, True, "unresolved shared writer", raw
        if bound:
            mode,cap,owed,why=bound
            if mode=="family":
                selected=(selected&cap)|owed
            elif mode=="guarded" and hot and protected!=ix.all:
                selected=(selected&cap)|protected|owed
        else:
            why="release static analysis"
        if selected.bit_count() >= 100:
            from static_bounds import coverage_bound
            bound = coverage_bound(self.team, ix, changes, hot, writers, protected)
            if bound is not None and selected & ~bound:
                selected &= bound
                why = "guarded body coverage"
        return selected,True,why,raw


def cpu_clock():
    import resource
    children=resource.getrusage(resource.RUSAGE_CHILDREN)
    return process_time()+children.ru_utime+children.ru_stime


def run(out,root,data,app):
    start=monotonic()
    cpu_start=cpu_clock()
    paths=sorted((data/"commits").glob("*.patch"))
    if not paths:return
    tests=json.loads((data/"tests.json").read_bytes())["tests"]
    durations={t["number"]:int(t["seconds"]*1000+0.5) for t in tests}
    ranked=sorted(durations,key=lambda n:(-durations[n],n))
    full=allocate(set(ranked),ranked,durations)
    full_json=json.dumps(full,separators=(",",":"))
    plans={}
    try:
        selector=Selector(root,app)
        ix=selector.ix
        by_id={t["id"]:t["number"] for t in tests}
        numbers=[by_id.get(name) for name in ix.ids]
        missing=set(ranked)-set(numbers)
        reverse={by_id[n] for n in (
            "tests/dialects/test_dialect.py::TestDialect::test_enum",
            "tests/dialects/test_starrocks.py::TestStarrocks::test_time_slice_origin_roundtrip",
        ) if n in by_id}
        choices={}
        pending=[]
        deadline=start+BATCH_SECONDS
        trace = os.environ.get("W3_TRACE")
        retry = set()
        mandatory = {}
        analyzed = {}
        invalid = set()
        def initial(path):
            from static_bounds import stress_obligation
            changes = read_patch(path, root)
            return selector.draft(path, changes), stress_obligation(ix, changes)

        for path, row in bounded_results(paths, initial, deadline, per_commit=2):
            if row is None:
                # Invalid/unsupported patches have no admissible postimage.
                continue
            draft, mandatory[path] = row
            mask, add_reverse, why, done, weight = draft
            choices[path] = (mask, add_reverse, why)
            if not done:
                pending.append((weight, path))
                retry.add(path)

        def accept_static(path, row):
            if row is None:
                return
            retry.discard(path)
            mask, rev, reason, raw = row
            if raw is not None:
                analyzed[path] = raw
            if reason == "invalid Python postimage":
                invalid.add(path)
            if reason in ("unresolved shared writer", "invalid Python postimage"):
                choices[path] = (ix.all, True, reason)
            else:
                choices[path] = (choices[path][0] & mask, rev, reason)

        spent = cpu_clock() - cpu_start
        budget = max(0, 0.112 * len(paths) - spent - 0.045)
        from bounded_refine import refine
        for path, row in refine([p for _, p in sorted(pending)], selector.select, deadline, budget):
            accept_static(path, row)

        def numbers_for(mask, use_reverse):
            if mask == ix.all:
                return all_numbers
            required = missing.copy()
            while mask:
                bit = mask & -mask
                number = numbers[bit.bit_length() - 1]
                if number is not None:
                    required.add(number)
                mask ^= bit
            if required and use_reverse:
                required.update(reverse)
            return required

        from pricing import charge
        all_numbers = set(ranked)
        required = {}
        expensive = []

        def price(path):
            mask, rev, why = choices[path]
            keep = numbers_for(mask | mandatory[path], rev)
            required[path] = keep
            workers = full if keep == all_numbers else allocate(keep, ranked, durations)
            plans[path] = json.dumps(workers, separators=(",", ":"))
            bill = charge(workers, durations)
            # Near-full plans pay at least two extra worker fees above a dominant test.
            # A narrow plan pinned to one long test can go straight to the judge.
            costly = (keep == all_numbers or (bill >= 25000 and
                      bill >= 6000 + max((durations[n] for n in keep), default=0)))
            if trace:
                print("W3STATIC", json.dumps([path.stem, why, len(keep), bill]), file=sys.stderr)
            if costly and path not in invalid:
                expensive.append((path, bill))

        for path in choices:
            price(path)

        # A busy batch can exhaust Wave-2's shared syntax budget. Only expensive,
        # unfinished plans earn another bounded attempt before paying to warm a suite.
        targets = [path for path, _ in expensive if path in retry]
        for path, row in bounded_results(targets, selector.select, deadline, per_commit=1.6):
            accept_static(path, row)
        if targets:
            old = expensive
            expensive = []
            for path, _ in old:
                price(path)

        if expensive:
            # Prove that the release could only return full before paying to warm
            # it. Reuse the resulting snapshot obligation in the live analysis.
            from economics import preflight
            checks = [p for p, _ in expensive if p in analyzed and
                      (analyzed[p][4] or analyzed[p][1] == ix.all)]
            def feasible(path):
                selector.load_team()
                return preflight(selector.team, root, path, analyzed[path], numbers, durations)
            for path, verdict in bounded_results(checks, feasible, deadline, per_commit=1.6):
                if verdict is not None:
                    possible, snapshot = verdict
                    if possible:
                        analyzed[path] = (*analyzed[path], snapshot)
                    else:
                        invalid.add(path)
            expensive = [(p, bill) for p, bill in expensive if p not in invalid]

        if expensive:
            # A warm suite changes the economics of verifying a plan dominated by a long
            # test. Keep all cheap plans. Price remaining high bills from the saved draft.
            active = {path for path, _ in expensive}
            for path in choices:
                if path in active or path in invalid:
                    continue
                keep = required[path]
                if keep and max(durations[n] for n in keep) >= 20000:
                    workers = allocate(keep, ranked, durations)
                    bill = charge(workers, durations)
                    if bill >= 25000:
                        expensive.append((path, bill))
            from live import LiveVerifier, MAX_CPU_SECONDS
            live_paths = [p for p, _ in expensive]
            bounds = {p: (choices[p][0] | mandatory[p], mandatory[p]) for p in live_paths}
            live = LiveVerifier(root, live_paths, tests, ranked, durations, full, start,
                                len(ix.ids), analyzed, bounds)
            try:
                for i, (path, bill) in enumerate(expensive):
                    if monotonic() >= deadline - 0.5:
                        break
                    seconds = min(MAX_CPU_SECONDS, bill / 2000.0)
                    keep, cpu, route = live.request(i, seconds, deadline, numbers_for, required[path])
                    keep = keep | numbers_for(mandatory[path], False)
                    workers = allocate(keep, ranked, durations)
                    if charge(workers, durations) <= bill:
                        plans[path] = json.dumps(workers, separators=(",", ":"))
                    if trace:
                        print("W3LIVE", json.dumps([path.stem, route, cpu, bill,
                              charge(workers, durations)]), file=sys.stderr)
            finally:
                live.close()
    except Exception as exc:
        print("Wave-3 conservative fallback",type(exc).__name__,file=sys.stderr)
    for path in paths:
        out.write('{"commit":'+json.dumps(path.stem)+',"workers":'+plans.get(path,full_json)+'}\n')
