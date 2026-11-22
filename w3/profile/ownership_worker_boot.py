"""As sitecustomize.py on the pin profiler's PYTHONPATH, instrument spawned Python pool workers."""
import os
import sys
if os.getenv("BR_OWNERSHIP_WORKERS") and any("multiprocessing.spawn import spawn_main" in a for a in sys.orig_argv):
    import ownership_profile
    ownership_profile.worker_start()
