import os
import sys

if os.getenv("W2_VALUE_WORKERS") and any("multiprocessing.spawn import spawn_main" in a for a in sys.orig_argv):
    from pool_values import begin_worker
    begin_worker()
