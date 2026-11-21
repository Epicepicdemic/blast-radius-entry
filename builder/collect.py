"""Run the pinned suite, then reduce its trace into a deterministic dependency index."""
import os
import subprocess
import sys
import tempfile

from pathlib import Path
from cold import collect as collect_cold
from cold_merge import merge as merge_cold
from cases import collect_cases
from index import build

with tempfile.TemporaryDirectory() as directory:
    subprocess.run([sys.executable, "-m", "pytest", "-p", "trace_plugin", "-q", "tests"],
                   env={**os.environ, "BR_TRACES": directory}, check=True)
    build(directory, "/out/maps.json")

collect_cases(Path("/out"))

collect_cold(Path("/out"))
merge_cold(Path("/out"))
