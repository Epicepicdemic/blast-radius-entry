"""Fast loading of image-built data. marshal format matches the pinned interpreter."""
import json
import marshal
from pathlib import Path
import sys


def load(path, fast):
    path = Path(path)
    if fast and path.with_suffix(".bin").is_file():
        return marshal.loads(path.with_suffix(".bin").read_bytes())
    return json.loads(path.read_bytes())


if __name__ == "__main__":
    for arg in sys.argv[1:]:
        source = Path(arg)
        data = load(source, False)
        source.with_suffix(".bin").write_bytes(marshal.dumps(data))
        if source.name == "maps.json":
            source.with_name("test-count").write_text(str(len(data["ids"])))
