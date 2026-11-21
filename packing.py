"""Place required tests first. Extras may use only existing idle milliseconds."""
def pack(required, ranked, durations, preferred=()):
    if not required:
        return []
    ordered = [t for t in ranked if t in required]
    best_cost = float("inf")
    for count in range(1, min(8, len(ordered)) + 1):
        groups = [[] for _ in range(count)]
        loads = [0] * count
        for t in ordered:
            worker = loads.index(min(loads))
            groups[worker].append(t)
            loads[worker] += durations[t]
        groups = [group for group in groups if group]
        cost = max(loads) + 2000 * len(groups)
        if cost < best_cost:
            best_cost = cost
            best = groups
            free = [max(loads) - load for load in loads[:len(groups)]]
    # Place zero-ms tests even on a single fully occupied worker. Then fill
    # slack with related tests first, shortest first within each priority.
    extras = sorted((t for t in ranked if t not in required),
                    key=lambda t: (durations[t] != 0, t not in preferred, durations[t], t))
    for t in extras:
        worker = free.index(max(free))
        if durations[t] <= free[worker]:
            best[worker].append(t)
            free[worker] -= durations[t]
    return best
