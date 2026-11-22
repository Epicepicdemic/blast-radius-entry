"""Record non-passive reads, control operations and exceptions at clean source sites."""
import ast
import builtins
import collections
import dis
import functools
import gzip
import json
from pathlib import Path
import sys
import types
from enum import Enum
from concurrent.futures import ProcessPoolExecutor
import slots as contexts
import shape_values

rows=collections.defaultdict(set)
root='/sqlglot/'
plain=(bool,int,float,str,bytes,type(None))
containers=(tuple,list,dict,set,frozenset)
get=builtins.getattr

def unsafe(site):rows[site].add(contexts.where())

def attribute(site,obj,name):
    t=type(obj)
    if t.__getattribute__ is not object.__getattribute__:
        # Ordinary CPython list/string methods have fixed attribute resolution.
        if t not in plain+containers:unsafe(site)
    else:
        desc=next((vars(c)[name] for c in t.__mro__ if name in vars(c)),None)
        if desc is not None and hasattr(type(desc),'__get__') and type(desc) not in (types.MemberDescriptorType,types.FunctionType):unsafe(site)
        if desc is None and any('__getattr__' in vars(c) for c in t.__mro__):unsafe(site)
    return get(obj,name)

def subscript(site,obj,key):
    t=type(obj)
    if t in (list,tuple,str,bytes):
        if not (type(key) is int or type(key) is slice and all(type(x) in (int,type(None)) for x in (key.start,key.stop,key.step))):unsafe(site)
    elif t is dict:
        if type(key) not in (int,str,bytes) or not all(type(x) in plain for x in obj):unsafe(site)
    else:unsafe(site)
    return obj[key]

def operand(site,obj):
    if type(obj) not in plain+containers:unsafe(site)
    return obj

def iterate(site,obj):
    if type(obj) not in (list,tuple,str,bytes,dict,set,frozenset,range):unsafe(site)
    return obj

def compare(site,obj):
    if type(obj) not in plain and not (isinstance(obj,Enum) and type(obj).__eq__ in (int.__eq__,str.__eq__,object.__eq__)):unsafe(site)
    return obj

def contains(site,obj):
    if type(obj) not in (list,tuple,dict,set,frozenset,str,bytes):unsafe(site)
    elif type(obj) not in (str,bytes) and not all(type(x) in plain or isinstance(x,Enum) and type(x).__eq__ in (int.__eq__,str.__eq__,object.__eq__) for x in obj):unsafe(site)
    return obj

class RW(ast.NodeTransformer):
    def key(self,n):return ast.Constant(f'{self.path}:{n.lineno}:{n.col_offset}')
    def call(self,n,f,values):return ast.copy_location(ast.Call(ast.Name(f,ast.Load()),[self.key(n),*values],[]),n)
    def visit_Attribute(self,n):
        self.generic_visit(n)
        if id(n) in self.watch and isinstance(n.ctx,ast.Load):return self.call(n,'_br5_pa',[n.value,ast.Constant(n.attr)])
        return n
    def visit_Subscript(self,n):
        self.generic_visit(n)
        if id(n) in self.watch and isinstance(n.ctx,ast.Load):
            key=n.slice
            if isinstance(key,ast.Slice):key=ast.Call(ast.Name('_br5_builtin_slice',ast.Load()),[x if x is not None else ast.Constant(None) for x in (key.lower,key.upper,key.step)],[])
            return self.call(n,'_br5_ps',[n.value,key])
        return n
    def visit_BoolOp(self,n):
        self.generic_visit(n)
        if id(n) in self.watch:n.values=[self.call(n,'_br5_po',[v]) for v in n.values]
        return n
    def visit_Compare(self,n):
        self.generic_visit(n)
        if id(n) in self.watch and len(n.ops)==1 and not isinstance(n.ops[0],(ast.Is,ast.IsNot)):
            n.left=self.call(n,'_br5_pc',[n.left]);n.comparators[0]=self.call(n,'_br5_pm' if isinstance(n.ops[0],(ast.In,ast.NotIn)) else '_br5_pc',[n.comparators[0]])
        return n
    def visit_If(self,n):
        present=id(n.test) in self.watch;self.generic_visit(n)
        if present:n.test=self.call(n,'_br5_po',[n.test])
        return n
    def visit_comprehension(self,n):
        present=id(n.iter) in self.watch;self.generic_visit(n)
        if present:n.iter=self.call(n.iter,'_br5_pi',[n.iter])
        return n
    def visit_Call(self,n):
        name=n.func.id if isinstance(n.func,ast.Name) else None
        self.generic_visit(n)
        if id(n) in self.watch and name=='len' and len(n.args)==1 and not n.keywords:n.args[0]=self.call(n,'_br5_pi',[n.args[0]])
        return n

def sites(tree):
    # A deletable bookkeeping region consists of simple local assignments
    # around optional branches. Sampling is determined solely by pin syntax.
    watch=set()
    for fn in ast.walk(tree):
        if not isinstance(fn,ast.FunctionDef):continue
        for stmt in ast.walk(fn):
            for _,seq in ast.iter_fields(stmt):
                if not isinstance(seq,list) or not any(isinstance(x,ast.If) for x in seq):continue
                for st in seq:
                    if not isinstance(st,(ast.If,ast.Assign,ast.AnnAssign)):continue
                    for n in ast.walk(st):
                        if isinstance(n,(ast.Assign,ast.AnnAssign)) and n.value is not None and all(isinstance(t,ast.Name) for t in (n.targets if isinstance(n,ast.Assign) else [n.target])):v=n.value
                        elif isinstance(n,ast.If):v=n.test
                        else:continue
                        # Function calls are effect boundaries, with a special
                        # typed check for builtin len. Avoid profiling large SQL
                        # parser call trees whose removal owes their whole line.
                        if any(isinstance(z,ast.Call) and not (isinstance(z.func,ast.Name) and z.func.id=='len') for z in ast.walk(v)):continue
                        watch.update(id(x) for x in ast.walk(v))
    return watch
class Source(contexts.Source):
    def get_code(self,name):
        path=self.get_filename(name);tree=ast.parse(self.get_data(path),path);rw=RW();rw.path=str(Path(path).relative_to('/sqlglot'))
        if rw.path.startswith('sqlglot/'):
            rw.watch=sites(tree);rw.visit(tree)
        shape_values.rewrite(tree,rw.path)
        return compile(ast.fix_missing_locations(tree),path,'exec',dont_inherit=True)
class Finder(contexts.Finder):
    def find_spec(self,name,path,target=None):
        s=super().find_spec(name,path,target)
        if s:s.loader=Source(name,s.origin)
        return s
@functools.lru_cache(6000)
def code_lines(code):return {i.offset:i.positions.lineno for i in dis.get_instructions(code)}

def raised(code,offset,error):
    if type(error) is TypeError:
        # CPython argument-binding errors name the Python callable before its
        # frame is entered. Retain ambiguous binding errors as a wildcard.
        message = error.args[0] if len(error.args)==1 and type(error.args[0]) is str else ''
        if any(x in message for x in ('argument', 'keyword', 'positional')):
            receiver, sep, detail = message.partition('() ')
            if sep and receiver.endswith('.__init__'):
                unsafe('@argument-error/' + receiver)
            elif not sep and any(x in message for x in ('positional argument', 'keyword-only argument', 'multiple values for', 'unexpected keyword')):
                unsafe('@argument-error/*')
    if code.co_filename.startswith(root+'sqlglot/'):
        line=code_lines(code).get(offset)
        if line:unsafe(code.co_filename[len(root):]+':'+str(line)+':error')

def install():
    shape_values.setup(unsafe)
    for k,v in {'pa':attribute,'ps':subscript,'po':operand,'pi':iterate,'pc':compare,'pm':contains}.items():setattr(builtins,'_br5_'+k,v)
    builtins._br5_builtin_slice=slice
    mon=sys.monitoring;tool=3;mon.use_tool_id(tool,'clean read effects');mon.register_callback(tool,mon.events.RAISE,raised);mon.set_events(tool,mon.events.RAISE)
folder=Path('/tmp/br5-passive-workers');counts=collections.Counter()
ids=json.load(open('/app/maps.json'))['ids'];idx={n:i for i,n in enumerate(ids)}

def task(key,fn,a,kw):
    rows.clear();ready=hasattr(builtins,'_br5_pa') and any(type(f) is Finder for f in sys.meta_path)
    try:return fn(*a,**kw)
    finally:
        with gzip.open(folder/key,'wt') as f:json.dump(list(rows) if ready else None,f,separators=(',',':'))

def pytest_configure(config):
    contexts.pytest_configure(config);sys.meta_path[0]=Finder();install();folder.mkdir();orig=ProcessPoolExecutor.submit
    def submit(pool,fn,*a,**kw):
        ctx=contexts.where()
        if ctx not in idx:return orig(pool,fn,*a,**kw)
        counts[ctx]+=1
        return orig(pool,task,f'{idx[ctx]}.{counts[ctx]}.gz',fn,a,kw)
    ProcessPoolExecutor.submit=submit
pytest_collection_finish=contexts.pytest_collection_finish
pytest_runtest_protocol=contexts.pytest_runtest_protocol
pytest_fixture_setup=contexts.pytest_fixture_setup
pytest_runtest_logreport=contexts.pytest_runtest_logreport

def pytest_sessionfinish(session,exitstatus):
    assert not exitstatus and set(ids)<=contexts.passed
    opaque=set(contexts.opaque)
    for n,c in counts.items():
        for i in range(1,c+1):
            p=folder/f'{idx[n]}.{i}.gz'
            if not p.exists():break
            records=json.load(gzip.open(p))
            if records is None:break
            for site in records:rows[site].add(n)
        else:opaque.discard(n)
    anc=collections.defaultdict(int)
    for n,parents in contexts.contexts.items():
        if n in idx:
            for p in parents:anc[p]|=1<<idx[n]
    def encode(ts):
        m=0;mods=set()
        for t in ts:
            if t in idx:m|=1<<idx[t]
            elif t.startswith('@scope/'):m|=anc[t[7:]]
            elif t.startswith('@module/'):mods.add(t[8:])
            else:m=(1<<len(ids))-1
        return [hex(m),sorted(mods)]
    doc=dict(ids=ids,passed=sorted(contexts.passed),keyword_inventory=sorted(shape_values.words),opaque=encode(opaque),tasks=sum(counts.values()),rows=[[k,encode(ts)] for k,ts in sorted(rows.items())]);Path('/tmp/passive_ops.gz').write_bytes(gzip.compress(json.dumps(doc,separators=(',',':')).encode(),mtime=0))
