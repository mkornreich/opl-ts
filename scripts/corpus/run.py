"""Runs every model of an OPL corpus (see fetch.py) and groups the failures.

usage: python3 scripts/corpus/run.py corpus results.json   (after npm run build)
"""
import json, subprocess, sys, os, re, concurrent.futures as cf
from collections import Counter
if len(sys.argv) != 3 or sys.argv[1].startswith('-'):
    sys.exit(__doc__)
root, outname = sys.argv[1], sys.argv[2]
manifest = json.load(open(os.path.join(root, 'manifest.json')))
CLI = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'dist', 'src', 'cli.js')
def run(m):
    args = ['node', CLI, '-q', '--time-limit', '20', m['file'], *m['data']]
    try:
        r = subprocess.run(args, capture_output=True, text=True, timeout=45, cwd=os.path.dirname(m['file']))
    except subprocess.TimeoutExpired:
        return m, 'timeout', ''
    out = r.stdout + r.stderr
    err = [l for l in out.splitlines() if l.startswith('error:') or l.startswith('Error') or 'TypeError' in l or 'RangeError' in l]
    if r.returncode != 0 or err:
        return m, 'error', (err[0] if err else (out.strip().splitlines() or [f'exit {r.returncode}'])[-1])
    return m, 'ok', (out.strip().splitlines() or [''])[0]
results = []
with cf.ThreadPoolExecutor(8) as ex:
    for m, st, msg in ex.map(run, manifest):
        results.append({'file': m['file'], 'repo': m['repo'], 'path': m['path'], 'status': st, 'msg': msg})
json.dump(results, open(os.path.join(root, outname), 'w'), indent=1)
print(Counter(r['status'] for r in results))
def norm(msg):
    msg = re.sub(r'^error: .*?:\d+:\d+: ', '', msg)
    return re.sub(r"'[^']*'", "'X'", msg)[:100]
for k, v in Counter(norm(r['msg']) for r in results if r['status'] != 'ok').most_common(45): print(v, k)
