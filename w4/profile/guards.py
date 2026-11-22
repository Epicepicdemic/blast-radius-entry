"""Record short-circuit operands whose evaluation can be erased without invoking user code."""
import ast,builtins,collections,gzip,json,sys
import slots as s
rows=collections.defaultdict(lambda:collections.defaultdict(set))
def pure(n):
    if isinstance(n,(ast.Name,ast.Constant)):return True
    if isinstance(n,ast.Compare):
        return len(n.ops)==1 and isinstance(n.ops[0],(ast.Is,ast.IsNot)) and all(isinstance(k,(ast.Name,ast.Constant)) for k in [n.left,*n.comparators])
    if isinstance(n,ast.UnaryOp):return isinstance(n.op,ast.Not) and pure(n.operand)
    return isinstance(n,ast.BoolOp) and all(pure(x) for x in n.values)
def note(site,value):
    t=type(value)
    b=bool(value) if t in (bool,int,str,type(None),list,tuple,dict,set,frozenset) else None
    rows[site][str(b)].add(s.where())
    return value
class Rewrite(ast.NodeTransformer):
    def visit_BoolOp(self,n):
        original=list(n.values)
        self.generic_visit(n)
        for i,operand in enumerate(original[:-1]):
            if pure(operand):
                k=f"{self.path}:{n.lineno}:{n.col_offset}:{i}"
                n.values[i]=ast.copy_location(ast.Call(ast.Name('_br4_guard',ast.Load()),[ast.Constant(k),n.values[i]],[]),operand)
        return n
class Source(s.Source):
    def get_code(self,name):
        path=self.get_filename(name);rw=Rewrite()
        rw.path=str(s.Path(path).relative_to(s.ROOT))
        return compile(ast.fix_missing_locations(rw.visit(ast.parse(self.get_data(path),path))),path,'exec',dont_inherit=True)
class Finder(s.Finder):
    def find_spec(self,name,path,target=None):
        p=super().find_spec(name,path,target)
        if p:p.loader=Source(name,p.origin)
        return p
def pytest_configure(config):
    s.pytest_configure(config);builtins._br4_guard=note;sys.meta_path[0]=Finder()
pytest_collection_finish=s.pytest_collection_finish
pytest_runtest_protocol=s.pytest_runtest_protocol
pytest_fixture_setup=s.pytest_fixture_setup
pytest_runtest_logreport=s.pytest_runtest_logreport
def pytest_sessionfinish(session,exitstatus):
    assert not exitstatus
    ids=json.load(open('/app/maps.json'))['ids'];idx={x:i for i,x in enumerate(ids)};anc=collections.defaultdict(int)
    unseen=set(ids)-s.passed
    assert len(unseen)<8
    for t,chain in s.contexts.items():
        if t in idx:
            for x in chain:anc[x]|=1<<idx[t]
    def encode(seen):
        m=0;modules=[]
        for x in seen:
            if x in idx:m|=1<<idx[x]
            elif x.startswith('@scope/'):m|=anc[x[7:]]
            elif x.startswith('@module/'):modules.append(x[8:])
            else:m=(1<<len(ids))-1
        return hex(m),sorted(modules)
    with gzip.open('/tmp/guards.gz','wt') as f:
        json.dump(dict(ids=ids,opaque=encode(unseen|s.opaque),sites={k:{v:encode(t) for v,t in d.items()} for k,d in rows.items() if k.startswith('sqlglot/')}),f,separators=(',',':'))
