"""Reject live work only when the release cannot discharge the required obligations."""
from patching import read_patch


def preflight(index, root, path, raw, numbers, durations):
    from selector import equal_trees
    selected, protected, _, hot, writers, _ = raw
    if writers:
        # The release's maximum vanilla budget is five CPU seconds and its scheduler
        # admits at most 1,500 measured milliseconds. Every writer must complete.
        from verify import runnable
        minimum = 75 if hot is not None else 280
        total = 0
        left = writers
        while left:
            bit = left & -left
            i = bit.bit_length() - 1
            number = numbers[i]
            if number is None or not runnable(index.ids[i]):
                return False, None
            total += durations[number] + 2
            left ^= bit
        if total > 1500 or 2 * (minimum + total + 100 * writers.bit_count()) >= 5000:
            return False, None
        if selected == protected:
            return False, None
        return True, None
    if selected != index.all or protected != index.all:
        return True, None
    from snapshot_cone import runtime_readers
    changes = read_patch(path, root)
    snap = runtime_readers(index, changes, equal_trees)
    if snap is None:
        from module_gate import candidate
        return candidate(index, changes, None, equal_trees) is not None, None
    # Even a perfect import-state match must retain every runtime reader.
    return snap[1] != index.all, snap
