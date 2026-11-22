"""Install the Wave-3 layer beside the verified, built team entry."""
import argparse
from pathlib import Path
import shutil
import subprocess
import sys
from build_index import build

def install(app,src,pin,reindex=True):
    # Verify and apply the integration hooks against the exact PB selector.
    import hashlib
    sys.path.insert(0, str(app.resolve()))
    from patching import apply_patch
    hashes = {
        "selector": "dedcf1d61e5bf82934cb3194596f4fc358b8c7b1001bc399e4440dbbab95406b",
        "verify": "cd57faf351066b2566d8e158e4c4f25748b22fd8a8636142466b069c485984ea",
        "heavy_reach": "266db98d598108cd0bca808aabe253ca48cece9ded1c2d04d14b3d746c2c3baf",
    }
    for name, digest in hashes.items():
        path = app / (name + ".py")
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError("expected " + name + " from 5d6d8aa")
        [change] = apply_patch((src / (name + ".patch")).read_bytes(), app.resolve())
        if change.path != path.name:
            raise ValueError("unexpected patch target")
        path.write_bytes(change.after)
    names = ("bounded_refine", "regions", "fast_select", "value_bounds", "impact",
             "callback_equivalence", "pricing", "economics", "ownership", "branch_reach", "live", "static_bounds", "module_gate", "module_reads", "coverage_skip", "wave3_entry")
    for name in names:
        shutil.copyfile(src / (name + ".py"), app / (name + ".py"))
    shutil.copyfile(src / "profile/branches.json.gz", app / "branches.json.gz")
    if reindex:
        build(pin,app/"maps.json",src/"profile",app/"impact.bin")
        script = """import marshal,sys
from pathlib import Path
from selector import load_index
from state_watch import persistent_readers
from verify import WarmSuite
pin,output=map(Path,sys.argv[1:])
ix=load_index(pin)
suite=WarmSuite(pin,ix.ids)
suite.warm()
output.write_bytes(marshal.dumps(persistent_readers(ix)))
"""
        subprocess.run([sys.executable,"-B","-c",script,str(pin.resolve()),str((app/"shared.bin").resolve())],
                       cwd=app,check=True)
if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("--app",type=Path,required=True)
    p.add_argument("--pin",type=Path,required=True)
    p.add_argument("--code-only",action="store_true")
    a=p.parse_args()
    install(a.app,Path(__file__).resolve().parent,a.pin,not a.code_only)
