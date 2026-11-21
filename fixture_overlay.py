"""Serve read-only SQL text fixtures from Linux memory-backed file descriptors."""
import builtins
import io
import os


class Fixtures:
    def __init__(self, root, changes):
        self.files = {}
        self.seen = set()
        self.unfaithful = False
        self.opening = None
        for change in changes:
            if not change.path.endswith(".sql"):
                continue
            fd = os.memfd_create("sql-fixture")
            with os.fdopen(fd, "wb", closefd=False) as stream:
                stream.write(change.after)
            self.files[str(root / change.path)] = f"/proc/self/fd/{fd}"

    def install(self):
        if not self.files:
            return

        def wrap(original):
            def opened(file, mode="r", buffering=-1, encoding=None, errors=None,
                       newline=None, closefd=True, opener=None):
                if isinstance(file, int):
                    return original(file, mode, buffering, encoding, errors, newline, closefd, opener)
                path = os.path.abspath(os.fsdecode(file))
                if path in self.files:
                    if mode not in ("r", "rt", "rb") or opener is not None:
                        self.unfaithful = True
                        raise OSError("unsupported access to an overlaid fixture")
                    self.seen.add(path)
                    def memory_opener(_path, flags):
                        return os.open(self.files[path], flags)
                    self.opening = path
                    try:
                        return original(file, mode, buffering, encoding, errors, newline, closefd, memory_opener)
                    finally:
                        self.opening = None
                return original(file, mode, buffering, encoding, errors, newline, closefd, opener)
            return opened

        builtins.open = wrap(builtins.open)
        io.open = wrap(io.open)
