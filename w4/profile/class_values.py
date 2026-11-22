"""Observe read sites for immutable scalar dialect/class options on the pinned program."""
import ast,builtins,collections,functools,gzip,json,sys
from pathlib import Path
import slots as scopes
hits=collections.defaultdict(set)
fields=set()
def scalar(n):
    try:return type(ast.literal_eval(n)) in (bool,type(None),str,int,float)
    except (TypeError,ValueError):return False
for f in Path('/sqlglot/sqlglot').rglob('*.py'):
    for cls in (n for n in ast.walk(ast.parse(f.read_bytes())) if isinstance(n,ast.ClassDef)):
        for st in cls.body:
            if isinstance(st,(ast.Assign,ast.AnnAssign)) and scalar(st.value):
                for t in st.targets if isinstance(st,ast.Assign) else [st.target]:
                    if isinstance(t,ast.Name) and t.id.isupper():fields.add(t.id)
@functools.lru_cache(None)
def owners(cls,field):
    return [base.__module__+'.'+base.__qualname__+'.'+field for base in type.__getattribute__(cls,'__mro__')
            if base.__module__.startswith('sqlglot.') and field in vars(base)]
def record(obj,f):
    c=obj if isinstance(obj,type) else type(obj)
    for q in owners(c,f):hits[q].add(scopes.where())
    return getattr(obj,f)
class Rewrite(ast.NodeTransformer):
    def visit_Attribute(self,n):
        self.generic_visit(n)
        if isinstance(n.ctx,ast.Load) and n.attr in fields:return ast.copy_location(ast.Call(ast.Name('_br4_value',ast.Load()),[n.value,ast.Constant(n.attr)],[]),n)
        return n
class Source(scopes.Source):
    def get_code(self,name):
        p=self.get_filename(name)
        return compile(ast.fix_missing_locations(Rewrite().visit(ast.parse(self.get_data(p),p))),p,'exec',dont_inherit=True)
class Finder(scopes.Finder):
    def find_spec(self,name,path,target=None):
        s=super().find_spec(name,path,target)
        if s:s.loader=Source(name,s.origin)
        return s
def pytest_configure(config):
    scopes.pytest_configure(config)
    builtins._br4_value=record
    sys.meta_path[0]=Finder()
pytest_collection_finish=scopes.pytest_collection_finish
pytest_runtest_protocol=scopes.pytest_runtest_protocol
pytest_fixture_setup=scopes.pytest_fixture_setup
pytest_runtest_logreport=scopes.pytest_runtest_logreport
def pytest_sessionfinish(session,exitstatus):
    assert not exitstatus
    ids=json.load(open('/app/maps.json'))['ids'];index={s:i for i,s in enumerate(ids)}
    unread=set(ids)-scopes.passed
    assert len(unread)<=8
    anc=collections.defaultdict(int)
    for item,chain in scopes.contexts.items():
        if item in index:
            for node in chain:anc[node]|=1<<index[item]
    def mask(values):
        out=0;mods=[]
        for s in values:
            if s in index:out|=1<<index[s]
            elif s.startswith('@scope/'):out|=anc[s[7:]]
            elif s.startswith('@module/'):mods.append(s[8:])
            else:out=(1<<len(ids))-1
        return hex(out),sorted(mods)
    with gzip.open('/tmp/class-values.gz','wt') as f:
        json.dump(dict(ids=ids,opaque=mask(unread|scopes.opaque),fields=sorted(fields),rows={k:mask(v) for k,v in hits.items()}),f,separators=(',',':'))
