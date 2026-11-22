"""Only a gate price. Every removal of a runnable candidate still needs a successful receipt."""
def cost_lower_bound(numbers,durations):
    if not numbers:return 0
    total=largest=0
    for n in numbers:
        d=durations[n]
        total+=d
        if d>largest:largest=d
    return min(2000*k+max(largest,(total+k-1)//k) for k in range(1,min(8,len(numbers))+1))

def allocate(required, ranked, durations):
    """Choose the same best LPT bill while skipping worker counts that cannot improve it."""
    if not required:
        return []
    ordered=[n for n in ranked if n in required]
    total=sum(durations[n] for n in ordered)
    largest=durations[ordered[0]]
    choices=sorted((2_000*k+max(largest,(total+k-1)//k),k)
                   for k in range(1,min(8,len(ordered))+1))
    best_cost=float("inf")
    best_count=9
    best=None
    for lower,k in choices:
        if lower>best_cost or (lower==best_cost and k>=best_count):
            continue
        loads=[0]*k
        groups=[[] for _ in loads]
        for n in ordered:
            j=loads.index(min(loads))
            groups[j].append(n)
            loads[j]+=durations[n]
        groups=[g for g in groups if g]
        cost=2_000*len(groups)+max(loads)
        if (cost,k)<(best_cost,best_count):
            best_cost,best_count,best=cost,k,groups
    return best

def charge(workers,durations):
    return 2_000*len(workers)+max((sum(durations[n] for n in w) for w in workers),default=0)
