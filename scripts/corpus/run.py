"""Runs every model of an OPL corpus (see fetch.py) and groups the failures.

usage: python3 scripts/corpus/run.py corpus results.json [time-limit-seconds]   (after npm run build)

Each model runs in its own process with a time limit; a watchdog kills a
process that uses more than 2.5 GB, at most two run at once, and a new one only
starts while the machine has at least 12 GB available.
"""
import json, os, re, subprocess, sys, threading, time, concurrent.futures as cf
from collections import Counter

CLI = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'dist', 'src', 'cli.js')
MAX_RSS = 2.5 * 1024 ** 3
MIN_AVAILABLE = 12 * 1024 ** 3
PARALLEL = 2
_start_lock = threading.Lock()


def available_memory():
    with open('/proc/meminfo') as f:
        for line in f:
            if line.startswith('MemAvailable:'):
                return int(line.split()[1]) * 1024
    return MIN_AVAILABLE


def rss(pid):
    try:
        with open(f'/proc/{pid}/status') as f:
            for line in f:
                if line.startswith('VmRSS:'):
                    return int(line.split()[1]) * 1024
    except OSError:
        pass
    return 0


def run_guarded(args, cwd, timeout):
    """Runs a command; returns (status, output) with status ok / error / timeout / memory."""
    with _start_lock:
        while available_memory() < MIN_AVAILABLE:
            time.sleep(1)
        p = subprocess.Popen(args, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                             env={**os.environ, 'OPL_MEMORY_LIMIT_MB': '2048'})
    out = []
    reader = threading.Thread(target=lambda: out.append(p.stdout.read()))
    reader.start()
    start, status = time.time(), None
    while p.poll() is None:
        if rss(p.pid) > MAX_RSS or available_memory() < MIN_AVAILABLE / 3:
            p.kill()
            status = 'memory'
        elif time.time() - start > timeout:
            p.kill()
            status = 'timeout'
        time.sleep(0.2)
    reader.join()
    return status or ('error' if p.returncode else 'ok'), ''.join(out)


def run(m, limit):
    status, out = run_guarded(['node', CLI, '-q', '--time-limit', str(limit), m['file'], *m['data']],
                              os.path.dirname(m['file']), limit * 2 + 20)
    lines = out.strip().splitlines()
    err = [l for l in lines if l.startswith('error:') or re.search(r'\b[A-Z]\w*Error:', l)]
    if status == 'ok' and err:
        status = 'error'
    msg = err[0] if err else (lines[0] if lines else '')
    if status == 'ok' and ('within the limits' in msg or 'limit reached' in msg):
        status = 'limit'
    return m, status, msg


def main():
    if len(sys.argv) not in (3, 4) or sys.argv[1].startswith('-'):
        sys.exit(__doc__)
    root, outname = sys.argv[1], sys.argv[2]
    limit = int(sys.argv[3]) if len(sys.argv) == 4 else 20
    manifest = json.load(open(os.path.join(root, 'manifest.json')))
    results = []
    with cf.ThreadPoolExecutor(PARALLEL) as ex:
        for m, st, msg in ex.map(lambda m: run(m, limit), manifest):
            results.append({'file': m['file'], 'repo': m['repo'], 'path': m['path'], 'status': st, 'msg': msg})
    json.dump(results, open(os.path.join(root, outname), 'w'), indent=1)
    print(Counter(r['status'] for r in results))

    def norm(msg):
        msg = re.sub(r'^error: .*?:\d+:\d+: ', '', msg)
        return re.sub(r"'[^']*'", "'X'", msg)[:100]
    for k, v in Counter(norm(r['msg']) for r in results if r['status'] != 'ok').most_common(45):
        print(v, k)


if __name__ == '__main__':
    main()
