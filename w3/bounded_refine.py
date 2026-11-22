"""A cumulative CPU timer in the persistent analysis child. A timeout discards its caches."""
import signal
from time import process_time
from bounded_batch import bounded_results

def refine(paths,analyze,deadline,budget):
    if not paths or budget<=0:
        return
    remaining=budget
    armed=False
    def timed(path):
        nonlocal armed
        if not armed:
            signal.signal(signal.SIGPROF,signal.SIG_DFL)
            signal.setitimer(signal.ITIMER_PROF,remaining)
            armed=True
        start=process_time()
        try:
            answer=analyze(path)
        except (ValueError,SyntaxError,RecursionError,OverflowError):
            answer=None
        return answer,process_time()-start
    it=bounded_results(paths,timed,deadline,per_commit=4)
    try:
        for path,row in it:
            if row is None:
                # Could be a killed/exhausted worker. Never grant another fresh CPU allowance.
                break
            answer,delta=row
            remaining-=delta
            yield path,answer
            if remaining<=0:break
    finally:
        it.close()
