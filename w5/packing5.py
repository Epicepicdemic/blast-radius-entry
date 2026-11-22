"""Tighten small uneven LPT schedules with bounded best-fit bin packing."""
from pricing import charge


def improve(groups, required, ranked, durations):
    if len(required)<3 or len(required)>220 or not groups:
        return groups
    items=[n for n in ranked if n in required]
    total=sum(durations[n] for n in items)
    largest=durations[items[0]]
    best=charge(groups,durations)
    for k in range(2,min(8,len(items))+1):
        lower=max(largest,(total+k-1)//k)
        maximum=best-2000*k-1
        if lower>maximum:
            continue
        # Exact capacities are integral milliseconds. Each accepted solution is
        # checked by its own worker loads; failed trials make no optimality claim.
        for _ in range(6):
            limit=(lower+maximum)//2
            bins=[[] for i in range(k)];loads=[0]*k
            for n in items:
                size=durations[n]
                slots=[i for i,load in enumerate(loads) if load+size<=limit]
                if not slots:
                    lower=limit+1
                    break
                i=max(slots,key=loads.__getitem__)
                bins[i].append(n);loads[i]+=size
            else:
                actual=[b for b in bins if b]
                price=charge(actual,durations)
                if price<best:best=price;groups=actual
                maximum=min(limit-1,best-2000*k-1)
            if lower>maximum:break
    return groups
