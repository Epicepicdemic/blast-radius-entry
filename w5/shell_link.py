"""Index observed write receivers by lexical scope and expression, independent of patch coordinates."""
import ast, collections, gzip, json
from pathlib import Path

def build(root,ix,expand):
    doc=json.load(gzip.open(Path("/w5/profile/write_shells.json.gz")))
    assert doc["ids"]==ix.ids and set(doc["passed"])==set(ix.ids)
    if any(site.count(':')!=4 for site in doc['shells']):
        return {}, {}, {}, ix.all, {}
    from bounds import pool_facts
    from impact import disjoint_ranges
    opaque=expand(doc['opaque'])
    workers=pool_facts()
    positions=collections.defaultdict(dict)
    direct={}
    line_masks={}
    def covered(path,first,last):
        key=(path,first,last)
        if key not in line_masks:
            sec=ix.section(path)
            if not sec or 'lines' not in sec or any(first<=p<=last for p in sec['warm_unknown']+sec['order']):
                mask=ix.all
            else:
                mask=disjoint_ranges(sec,[(first,last)],ix)
                for n in range(first,last+1):mask|=workers['lines'].get(path,{}).get(n,0)
            line_masks[key]=mask
        return line_masks[key]
    for site,info in doc["shells"].items():
        p,line,col,end,ec=site.rsplit(":",4)
        point=(int(line),int(col),int(end),int(ec))
        if covered(p,point[0],point[2]) & opaque:
            info=[['*'],True,True]
        elif not info[1] and not info[2] and '*' not in info[0]:
            direct[p,*point]=frozenset(info[0])
        positions[p][point]=info
    by_expr=collections.defaultdict(list)
    for path,pos in positions.items():
        tree=ast.parse((root/path).read_bytes())
        def visit(n,qual):
            if isinstance(n,ast.ClassDef):qual+=n.name+"."
            if isinstance(n,ast.FunctionDef):qual+=n.name+".<locals>."
            if isinstance(n,ast.expr):
                point=(n.lineno,n.col_offset,n.end_lineno,n.end_col_offset)
                if point in pos:
                    by_expr[path,qual.removesuffix(".<locals>."),ast.dump(n)].append(pos[point])
            for c in ast.iter_child_nodes(n):visit(c,qual)
        visit(tree,"")
    safe={}
    observed={}
    for k,rows in by_expr.items():
        typs=set().union(*(v[0] for v in rows))
        if typs and "*" not in typs:observed[k]=typs
        if typs and "*" not in typs and all(not r[1] and not r[2] for r in rows):
            safe[k]=typs
    outside={(mod,n):expand(ctx) for (mod,n),ctx in doc["external"]}
    return safe,observed,outside,opaque,direct
