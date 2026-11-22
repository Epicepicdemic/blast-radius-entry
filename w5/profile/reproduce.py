"""Recollect pin observations in a sealed container with no evaluation inputs mounted."""
import argparse
import gzip
import hashlib
import json
from pathlib import Path
import subprocess

WORKERS = {
    'operands': '', 'operand_workers': 'operands', 'observers': '',
    'write_shells': '', 'field_uses': 'fields', 'dispatch_uses': 'dispatch',
    'prefixes': 'prefixes', 'passive_ops': 'passive',
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path)
    parser.add_argument('profiles', nargs='*')
    parser.add_argument('--image', default='blast-entry-wave5')
    parser.add_argument('--engine', default='docker')
    parser.add_argument('--cores')
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    for name in args.profiles or WORKERS:
        if name not in WORKERS:
            parser.error(f'Unknown profile {name!r}')
        path = args.output / (name + '.json.gz')
        log = args.output / (name + '.log')
        fresh = path.with_suffix('.tmp')
        flags = ['--cpuset-cpus', args.cores] if args.cores else []
        boot = WORKERS[name]
        extra = ['-e','BR5_PIN_WORKER='+boot] if boot else []
        py_path = ('/collect/worker_boot:' if boot else '') + '/sqlglot:/collect:/w4/profile'
        cmd = [args.engine,'run','--rm','--pull','never','--platform','linux/amd64',
               '--network','none','--read-only','--user','65534:65534','--cpus','2',
               '--memory','4g','--tmpfs','/tmp:rw,size=512m,mode=1777','--cap-drop','ALL',
               *flags,'-w','/sqlglot','-e','HOME=/tmp','-e','PYTHON_CPU_COUNT=2',
               '-e','PYTHONHASHSEED=0','-e','PYTHONPATH='+py_path,*extra,
               '-v',str(Path(__file__).resolve().parent)+':/collect:ro','--entrypoint','sh',
               args.image,'-ec','python -m pytest tests -p "$1" -p no:cacheprovider -q --tb=line --timeout=600 >&2 && cat "/tmp/$1.gz"',
               'collect',name]
        with fresh.open('wb') as stream, log.open('wb') as errors:
            try:
                subprocess.run(cmd, stdout=stream, stderr=errors, check=True)
            except subprocess.CalledProcessError:
                fresh.unlink(missing_ok=True)
                raise
        with gzip.open(fresh) as record:
            data=json.load(record)
        if not data['ids'] or len(data['ids']) != len(set(data['ids'])):
            raise ValueError('Invalid test identity list')
        if 'passed' in data and not set(data['ids']) <= set(data['passed']):
            raise ValueError('Incomplete clean suite')
        fresh.replace(path)
        print(name, hashlib.sha256(path.read_bytes()).hexdigest(), flush=True)


if __name__ == '__main__':
    main()
