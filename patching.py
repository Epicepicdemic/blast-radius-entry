"""Strictly apply text hunks to pinned bytes. Unsupported metadata widens selection."""
from bisect import bisect_left
from dataclasses import dataclass, field
from functools import lru_cache
from pathlib import Path
import re


MAX_CHANGED_LINES = 2000
MAX_PATCH_BYTES = 1024 * 1024


def overlaps(sorted_points, first, last):
    i = bisect_left(sorted_points, first)
    return i < len(sorted_points) and sorted_points[i] <= last


class UnknownPatch(ValueError):
    pass


@dataclass
class Change:
    path: str
    before: bytes
    after: bytes
    removed: set = field(default_factory=set)
    # Between old lines n and n+1, including n=0 at BOF.
    insertions: set = field(default_factory=set)
    # Physical line numbers in the reconstructed new file.
    added: set = field(default_factory=set)
    # New-file boundary after removing a line, including deletions with no additions.
    deletions: set = field(default_factory=set)


HUNK = re.compile(rb"@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@[^\n]*(?:\n|$)")
INDEX = re.compile(rb"index [0-9a-f]+\.\.[0-9a-f]+(?: 100(?:644|755))?\n")
NO_EOL = b"\\ No newline at end of file"


@lru_cache(maxsize=128)
def base(root, path):
    location = root / path
    if not location.resolve().is_relative_to(root) or not location.is_file():
        raise UnknownPatch("unknown source")
    return location.read_bytes()


def lf_lines(data):
    # splitlines() would split form feeds and other legal source bytes.
    parts = data.split(b"\n")
    return [p + b"\n" for p in parts[:-1]] + ([parts[-1]] if parts[-1] else [])


def read_patch(path, root):
    with path.open("rb") as stream:
        return apply_patch(stream.read(MAX_PATCH_BYTES + 1), root)


def apply_patch(raw, root):
    if len(raw) > MAX_PATCH_BYTES:
        raise UnknownPatch("patch byte limit")
    # Fast lower bound before splitting or opening any source file. A data
    # line resembling a file header is counted exactly inside the hunk below.
    marked = raw.count(b"\n+") + raw.count(b"\n-")
    headers = raw.count(b"\n+++ b/") + raw.count(b"\n--- a/")
    if marked - headers > MAX_CHANGED_LINES:
        raise UnknownPatch("changed line limit")
    changed_lines = 0
    lines = lf_lines(raw)
    i = 0
    seen = set()
    changes = []
    while i < len(lines):
        header = None
        if lines[i].startswith(b"diff --git "):
            header = lines[i][11:].rstrip(b"\n")
            i += 1
            if i < len(lines) and INDEX.fullmatch(lines[i]):
                i += 1
        if i + 1 >= len(lines) or not lines[i].startswith(b"--- a/") or not lines[i+1].startswith(b"+++ b/"):
            raise UnknownPatch("missing file headers or unsupported metadata")
        name = lines[i][6:].rstrip(b"\n")
        new = lines[i+1][6:].rstrip(b"\n")
        if new != name or (header is not None and header != b"a/" + name + b" b/" + name):
            raise UnknownPatch("inconsistent file names")
        path = name.decode("utf-8")
        if not path or any(x in ("", "..", ".") for x in path.split("/")) or path in seen:
            raise UnknownPatch("unsafe or repeated path")
        seen.add(path)
        i += 2
        before = base(root, path)
        old = lf_lines(before)
        result = []
        removed, insertions, added, deletions = set(), set(), set(), set()
        cursor = 0
        if i >= len(lines) or not HUNK.fullmatch(lines[i]):
            raise UnknownPatch("missing hunks")
        while i < len(lines) and (match := HUNK.fullmatch(lines[i])):
            start, old_count, new_start, new_count = (int(x) if x is not None else 1 for x in match.groups())
            start -= bool(old_count)
            new_start -= bool(new_count)
            if not cursor <= start <= len(old):
                raise UnknownPatch("overlapping hunks or base mismatch")
            result.extend(old[cursor:start])
            cursor = start
            if len(result) != new_start:
                raise UnknownPatch("new offset mismatch")
            i += 1
            consumed = emitted = 0
            old_layout, new_layout = [], []

            def end_block():
                # A changed suite boundary or newly introduced statement may
                # run on paths that did not reach any removed line.
                if new_layout != old_layout:
                    insertions.add(cursor)
                old_layout.clear()
                new_layout.clear()

            while consumed < old_count or emitted < new_count:
                if i >= len(lines) or lines[i][:1] not in (b" ", b"+", b"-"):
                    raise UnknownPatch("bad hunk body")
                op, payload = lines[i][:1], lines[i][1:]
                i += 1
                if i < len(lines) and lines[i].rstrip(b"\n") == NO_EOL:
                    payload = payload.removesuffix(b"\n")
                    i += 1
                if op == b" ":
                    end_block()
                else:
                    changed_lines += 1
                    if changed_lines > MAX_CHANGED_LINES:
                        raise UnknownPatch("changed line limit")
                if op != b"+":
                    if cursor >= len(old) or old[cursor] != payload:
                        raise UnknownPatch("old bytes differ")
                    cursor += 1
                    consumed += 1
                if op != b"-":
                    emitted += 1
                    result.append(payload)
                if op == b"-":
                    old_layout.append(payload[:len(payload) - len(payload.lstrip())])
                    removed.add(cursor)
                    deletions.add(len(result))
                elif op == b"+":
                    added.add(len(result))
                    new_layout.append(payload[:len(payload) - len(payload.lstrip())])
            end_block()
            if (consumed, emitted) != (old_count, new_count):
                raise UnknownPatch("hunk length mismatch")
        result.extend(old[cursor:])
        changes.append(Change(path, before, b"".join(result), removed, insertions, added, deletions))
    if not changes:
        raise UnknownPatch("no files")
    return changes
