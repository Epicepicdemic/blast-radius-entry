"""Build the supplementary pinned slots and expose the release's scoped effect report."""
import hashlib
from pathlib import Path
import shutil
import subprocess
import sys
app=Path("/app")
src=Path(__file__).parent
for name in ("bounds","frontier","namespaces","scalar_bounds","ownership_effects","read_effects","delayed","symbols","witness","compact","exception_arg","flow","signatures","guard_bounds","dispatch_bounds"):
    shutil.copyfile(src/(name+".py"),app/(name+".py"))
p=app/"cone.py"
old=p.read_text()
needle="    original, _ = index.select_changes(changes, effects=effects)"
assert old.count(needle)==1
p.write_text(old.replace(needle,needle+"\n    index.scoped_effects = effects"))
p=app/"shared_writes.py"
s=p.read_text()
needle="                            found_bindings.update(classified)"
assert s.count(needle)==1
s=s.replace(needle,"                            from read_effects import readonly\n                            if classified and readonly(arg,scope,node,census):\n                                continue\n"+needle)
needle="                                return True\n                            from read_effects import readonly"
assert s.count(needle)==1
s=s.replace(needle,"                                from read_effects import missing_call\n                                if missing_call(node,scope,census):\n                                    continue\n"+needle)
p.write_text(s)
p=app/"verify.py"
s=p.read_text()
needle="        self.incomplete |= 1 << self.indices[test]\n        super().addError(test, err)"
assert s.count(needle)==1
s=s.replace(needle,"""        # A synchronous application error raised inside the test body is a
        # completed writer observation. It never certifies that the test passed.
        tb=err[2]
        in_method=False
        while tb is not None:
            if tb.tb_frame.f_code is unittest.TestCase._callTestMethod.__code__:
                in_method=True
            tb=tb.tb_next
        if in_method and type(err[1]) in (NameError,UnboundLocalError,AttributeError,KeyError,IndexError,TypeError,ValueError) and self.fixtures.files.keys() <= self.fixtures.seen:
            self.observed |= 1 << self.indices[test]
        else:
            self.incomplete |= 1 << self.indices[test]
        super().addError(test, err)""")
needle='if not fixtures.files and heavy_reach.unchanged("tpc", changes, hot, screened_import=screened_import):'
assert s.count(needle)==1
s=s.replace(needle,'from signatures import unchanged as intact_rows\n            if not fixtures.files and (heavy_reach.unchanged("tpc", changes, hot, screened_import=screened_import) or intact_rows(changes, hot)):')
p.write_text(s)
subprocess.run([sys.executable,str(src/"link.py")],check=True)

shutil.copyfile(app/"wave3_entry.py",app/"wave4_entry.py")
