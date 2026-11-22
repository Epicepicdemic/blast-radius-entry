"""Build pin-only cold observations, then link them with warm coverage and source structure.
No patches, inventory durations, test outcomes on variants, or patch identifiers are inputs.
"""
import argparse
import ast
import gzip
import hashlib
import json
import marshal
import struct
import zlib
from collections import defaultdict
from callback_equivalence import freeze as freeze_callbacks
from regions import pin_regions
from pathlib import Path

MAGIC = b"BRCOLD2\0"

def read(path):
    return json.loads(path.read_bytes())

def read_gz(path):
    with gzip.open(path) as f:
        return json.load(f)

def freeze_cold(raw, maps, output):
    ids = read(maps)["ids"]
    loads, reads, lines = defaultdict(int), defaultdict(int), defaultdict(dict)
    for i, tid in enumerate(ids):
        receipt = read_gz(raw / f"{i}.json.gz")
        if receipt["id"] != tid or not receipt["lines"].get(tid.split("::")[0]):
            raise ValueError(f"incomplete cold node {i}")
        bit = 1 << i
        for path in set(receipt["loads"]) | receipt["lines"].keys():
            loads[path] |= bit
        for path in receipt["opens"]:
            reads[path] |= bit
        for path, points in receipt["lines"].items():
            if path.startswith(("tests/","sqlglot/","sqlglotc/")):
                row=lines[path]
                for n in points:
                    row[n]=row.get(n,0)|bit
    pool={}
    def handle(bits):
        return pool.setdefault(bits,len(pool))
    serialized = dict(ids=ids,loads={k:handle(v) for k,v in loads.items()},
        opens={k:handle(v) for k,v in reads.items()},
        lines={k:{n:handle(v) for n,v in vals.items()} for k,vals in lines.items()})
    serialized["masks"]=[hex(v) for v in pool]
    output.write_bytes(gzip.compress(json.dumps(serialized,separators=(",",":")).encode(),mtime=0))

def scope_tree(body,owner=""):
    for node in body:
        if isinstance(node,(ast.ClassDef,ast.FunctionDef,ast.AsyncFunctionDef)):
            name=owner+node.name
            yield name,node
            if isinstance(node,ast.ClassDef):
                yield from scope_tree(node.body,name+".")

def mod(path):
    return path.removesuffix(".py").replace("/",".").removesuffix(".__init__")

def build(pin, maps_file, profiles, output):
    warm=read(maps_file)
    cold=read_gz(profiles/"cold.json.gz")
    exposure=read_gz(profiles/"exposure.json.gz")
    keys=read_gz(profiles/"keys.json.gz")
    ids=warm["ids"]
    assert cold["ids"]==exposure["ids"]==keys["ids"]==ids and len(set(ids))==len(ids)
    assert exposure["collected"]==keys["passed"]==len(ids) and exposure["exitstatus"]==keys["exitstatus"]==0
    width=(len(ids)+7)//8
    all_bits=(1<<len(ids))-1
    cold_masks=[int(x,16) for x in cold["masks"]]
    warm_masks=[int(x,16) for x in warm["masks"]]
    def bits(table,k):
        idx=warm.get(table,{}).get(k)
        return 0 if idx is None else warm_masks[idx]
    pool={}
    def intern(mask):
        return pool.setdefault(mask,len(pool))
    files={}
    graph={}
    callers=defaultdict(int)
    exports={}
    hier={}
    global_reads=defaultdict(list)
    # Index per-source namespace uses, possible call targets, and class bases at image build.
    # These are over-approximations. Dynamic dispatch with no stronger bound uses the legacy guard.
    for path in sorted(warm["layout"]):
        tree=ast.parse((pin/path).read_bytes())
        local_lines={int(n):cold_masks[v] for n,v in cold["lines"].get(path,{}).items()}
        measured={int(n):warm_masks[v] for n,v in warm["lines"].get(path,{}).items()}
        funcs={}
        namespace=mod(path)
        stable=set()
        for statement in tree.body:
            if isinstance(statement,(ast.ClassDef,ast.FunctionDef,ast.AsyncFunctionDef)):stable.add(statement.name)
            if isinstance(statement,(ast.Import,ast.ImportFrom)):
                stable.update(a.asname or a.name.split(".")[0] for a in statement.names if a.name!="*")
            if isinstance(statement,(ast.AnnAssign,ast.Assign)) and statement.value is not None:
                targets=statement.targets if isinstance(statement,ast.Assign) else [statement.target]
                stable.update(t.id for t in targets if isinstance(t,ast.Name))
        exports[namespace]=sorted(stable)
        for name,n in scope_tree(tree.body):
            if isinstance(n,ast.ClassDef):
                hier[namespace+"."+name]=[ast.unparse(e) for e in n.bases]
            else:
                start=min([n.lineno]+[v.lineno for v in n.decorator_list])
                covered=0
                for j in range(n.body[0].lineno,n.end_lineno+1):
                    covered|=local_lines.get(j,0)
                reached=int(exposure["rows"].get(path,{}).get(name+":"+str(start),"0"),16)
                funcs[name]=(start,n.body[0].lineno,n.end_lineno,intern(covered|reached))
                calls={e.func.id if isinstance(e.func,ast.Name) else e.func.attr
                       for e in ast.walk(n) if isinstance(e,ast.Call) and isinstance(e.func,(ast.Name,ast.Attribute))}
                graph[namespace+"."+name]=sorted(calls)
                warm_reached=0
                for j in range(n.body[0].lineno,n.end_lineno+1):
                    warm_reached|=measured.get(j,0)
                for possible in calls:
                    callers[possible]|=covered|reached|warm_reached
        for n in ast.walk(tree):
            if isinstance(n,(ast.Name,ast.Attribute)) and isinstance(n.ctx,ast.Load):
                name=n.id if isinstance(n,ast.Name) else n.attr
                global_reads[name].append((path,n.lineno,isinstance(n,ast.Attribute)))
        cold_module=cold_masks[cold["loads"][path]] if path in cold["loads"] else 0
        opened=bits("opens",path)
        if path in cold["opens"]:
            opened|=cold_masks[cold["opens"][path]]
        warm_runtime=0
        for key,mask in exposure["rows"].get(path,{}).items():
            warm_runtime|=int(mask,16)
        for mask in exposure["rows"].get("@"+path,{}).values():
            warm_runtime|=int(mask,16)
        lambda_calls=defaultdict(int)
        for q,mask in exposure["rows"].get(path,{}).items():
            if q.rsplit(":",1)[0].endswith("<lambda>"):
                lambda_calls[int(q.rsplit(":",1)[1])]|=int(mask,16)
        regions,factories=pin_regions(tree,namespace,warm["factories"])
        files[path]=dict(regions=regions,factories=factories,lambda_calls={n:intern(m) for n,m in lambda_calls.items()},digest=hashlib.sha256((pin/path).read_bytes()).digest(),
            cold=intern(cold_module),observed=intern(warm_runtime),opens=intern(opened),
            functions=funcs, lines={n:intern(v) for n,v in measured.items()},
            cold_lines={n:intern(v) for n,v in local_lines.items()},
            order=warm.get("order_dependent_lines",{}).get(path,[]),
            warm_unknown=warm.get("warm_unknown",{}).get("lines",{}).get(path,[]))
    # Pin-time consumers of class registries can observe a failed or partial lazy load from another module.
    registry=0
    registry_names={"_classes","__subclasses__"}
    registry_locations=[]
    for name in registry_names|{"classes"}:
        for p,n,is_attribute in global_reads.get(name,()):
            if not is_attribute:continue
            # Class registration writes/reads in the metaclass itself occur at import.
            # Use the actual method's per-test CALL receipt below for those paths.
            if p=="sqlglot/dialects/dialect.py":
                # Keyed dispatch/registration itself is covered by the cold module receipt.
                # Whole-registry inspection, including the unknown-dialect diagnostic, escapes the key.
                src=(pin/p).read_text().splitlines()[n-1]
                if ".keys()" not in src:continue
            idx=warm["lines"].get(p,{}).get(str(n))
            if idx is not None:
                registry|=warm_masks[idx]
            registry_locations.append((p,n))
    owners=exposure["rows"].get("sqlglot/dialects/dialect.py",{})
    for name,v in owners.items():
        if name.split(":")[0] in ("_Dialect.classes","_Dialect.__iter__"):
            registry|=int(v,16)
    views={}
    for site,rows in keys["rows"].items():
        path,decl=site.split(":",1)
        views.setdefault(path,{})[decl]={k:intern(int(v,16)) for k,v in rows.items()}
    for p,entry in files.items():
        entry["keys"]=views.get(p,{})
    # Stress tests exercise resource limits that a cold functional path cannot certify after a
    # tokenizer table gains or loses keys. Identify them from the pin, not from failure history.
    id_positions={tid:i for i,tid in enumerate(ids)}
    stress=0
    for path in sorted({tid.split("::")[0] for tid in ids}):
        tree=ast.parse((pin/path).read_bytes())
        for name,n in scope_tree(tree.body):
            if not isinstance(n,ast.FunctionDef):continue
            tid=path+"::"+name.replace(".","::")
            if tid in id_positions and any(isinstance(v,ast.keyword) and v.arg=="max_nodes" for v in ast.walk(n)):
                stress|=1<<id_positions[tid]
    eager={"typing","__future__","builtins","sqlglot"}
    sources={mod(p):p for p in files}
    queue=["sqlglot"]
    while queue:
        q=queue.pop()
        for node in ast.parse((pin/sources[q]).read_bytes()).body:
            if isinstance(node,ast.ImportFrom) and not node.level and node.module:
                names=[node.module]
            elif isinstance(node,ast.Import):names=[v.name for v in node.names]
            else:continue
            for name in names:
                if name not in eager:
                    eager.add(name)
                    if name in sources:queue.append(name)
    seen_sources=set(files)
    extra=set(warm["opens"])|set(cold["opens"])
    for p in extra-seen_sources:
        c=cold_masks[cold["opens"][p]] if p in cold["opens"] else 0
        if not (pin/p).is_file() or not p.startswith(("tests/","sqlglot/","docs/")):continue
        files[p]=dict(opens=intern(bits("opens",p)|c),digest=hashlib.sha256((pin/p).read_bytes()).digest())
    for name in ("typing","builtins","__future__"):
        import importlib
        exports[name]=sorted(vars(importlib.import_module(name)))
    subscriber={name:intern(mask|bits("attributes",name)) for name,mask in callers.items()}
    callbacks=freeze_callbacks(pin,warm["layout"],exposure,warm,cold,ids,intern)
    # The optional profile contains observed inputs and call sites from the unchanged pin.
    values_file=profiles/"values.json.gz"
    values=read_gz(values_file) if values_file.exists() else {}
    if values and values["ids"] != ids:
        raise ValueError("value profile inventory mismatch")
    for key,forms in values.get("domains",{}).items():
        path,line,col=key.rsplit(":",2)
        if path in files:
            cols=files[path].setdefault("domains",{}).setdefault(int(line),{})
            cols[int(col)]=[(fact,intern(int(bits,16))) for fact,bits in forms]
    for key,bits0 in values.get("closures",{}).items():
        path,line,col=key.rsplit(":",2)
        if path in files:
            files[path].setdefault("closures",{})[int(line),int(col)]=intern(int(bits0,16))
    schema={k:{key:intern(int(mask,16)) for key,mask in vals.items()}
            for k,vals in values.get("schema",{}).items()}
    code_readers=bits("attributes","__code__")
    unknown_reflection=int(values.get("reflection_unknown",hex(all_bits)),16)
    other_reflection=bits("attributes","__closure__")|bits("attributes","getsource")|bits("attributes","getsourcelines")
    reflections={p:intern(int(m,16)&code_readers) for p,m in values.get("reflections",{}).items()}
    # Conservative first-divergence masks can be refined for solitary, unmodified constant returns.
    meta=dict(ids=ids,width=width,all=intern(all_bits),registry=intern(registry),
        unknown=intern(int(exposure["unknown"],16)|int(keys["unknown"],16)),
        schema_unknown=intern(int(values.get("schema_unknown",hex(all_bits)),16)),
        has_schema="schema" in values,value_unknown=intern(int(values.get("unknown",hex(all_bits)),16)),reflections=reflections,
        reflection_residual=intern((code_readers&unknown_reflection)|other_reflection|
                                   int(exposure["unknown"],16)|int(keys["unknown"],16)),
        stress=intern(stress),token_tables=warm["tokenizer_init_names"],eager=sorted(eager),
        reflection=intern(bits("attributes","__code__")|bits("attributes","__closure__")
                          |bits("attributes","getsource")|bits("attributes","getsourcelines")),
        graph_counts=(len(graph),sum(map(len,graph.values())),len(hier),sum(map(len,global_reads.values()))),
        paths={}, format=2)
    from ownership import link
    link(pin, files, read_gz(profiles/"ownership.json.gz"), ids, list(pool))
    blocks=[]
    offset=0
    for p,f in files.items():
        data=zlib.compress(marshal.dumps(f),6)
        meta["paths"][p]=(offset,len(data));blocks.append(data);offset+=len(data)
    # Export the graph for guarded lookups without charging a whole-project decode at batch startup.
    for name,section in [("@schema",schema),("@calls",graph),("@callbacks",callbacks),("@callers",subscriber),("@exports",exports),("@bases",hier),("@imports",warm["imports"]),("@registry_sites",registry_locations)]:
        data=zlib.compress(marshal.dumps(section),6)
        meta["paths"][name]=(offset,len(data));blocks.append(data);offset+=len(data)
    meta["unknown_opens"]=tuple(warm.get("warm_unknown",{}).get("opens",()))
    meta["mask_offset"]=offset
    header=marshal.dumps(meta)
    temp=output.with_suffix(".building")
    with temp.open("wb") as f:
        f.write(MAGIC+struct.pack("<I",len(header))+header)
        for chunk in blocks:f.write(chunk)
        for mask in pool:f.write(mask.to_bytes(width,"little"))
    temp.replace(output)
    print(f"{len(ids)} nodes, {len(files)} paths, {len(pool)} distinct masks, {output.stat().st_size} index bytes; graph counts {meta['graph_counts']}")

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--pin",type=Path)
    p.add_argument("--maps",required=True,type=Path)
    p.add_argument("--profiles",type=Path,default=Path(__file__).with_name("profile"))
    p.add_argument("--cold",type=Path,help="freeze the 1,620 individual pin-only cold trace records")
    p.add_argument("--output",type=Path,required=True)
    args=p.parse_args()
    if args.cold:freeze_cold(args.cold,args.maps,args.output)
    else:build(args.pin,args.maps,args.profiles,args.output)
