"""Downloads OPL models (and their .dat files) published on GitHub into a corpus folder.

usage: scripts/corpus/search.sh corpus   (search, needs `gh auth login`), then
       python3 scripts/corpus/fetch.py corpus
The files are third-party code: keep the corpus folder out of the repository.
"""
import subprocess, json, base64, os, sys, re
if len(sys.argv) != 2 or sys.argv[1].startswith('-'):
    sys.exit(__doc__)
root = sys.argv[1]
hits = [l.rstrip('\n').split('\t') for l in open(os.path.join(root, 'hits.tsv')) if l.strip()]
def gh(path):
    r = subprocess.run(['gh', 'api', path], capture_output=True, text=True)
    return json.loads(r.stdout) if r.returncode == 0 else None
files = os.path.join(root, 'files')
manifest, listed = [], {}
NMODL = re.compile(r'\b(BREAKPOINT|UNITS|SUFFIX|NEURON|ASSIGNED)\b|^\s*\(\*|\bIMPLEMENTATION MODULE\b|\bDEFINITION MODULE\b', re.M)
OPL = re.compile(r'\b(subject\s+to|solve\s*\{|dvar\b|var\s+\w+|minimize|maximize|constraints\s*\{)')
for repo, path, sha in hits:
    dest = os.path.join(files, repo.replace('/', '__'), path)
    if not os.path.exists(dest):
        blob = gh(f'repos/{repo}/git/blobs/{sha}')
        if not blob: continue
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        open(dest, 'wb').write(base64.b64decode(blob['content']))
    text = open(dest, 'rb').read().decode('utf8', 'replace')
    if not OPL.search(text) or NMODL.search(text):
        os.remove(dest); continue
    entry = {'repo': repo, 'path': path, 'file': dest, 'data': []}
    if re.search(r'=\s*\.\.\.', text):
        d = os.path.dirname(path)
        if (repo, d) not in listed:
            listing = gh(f'repos/{repo}/contents/{d}') or []
            listed[(repo, d)] = [x for x in listing if isinstance(x, dict)]
        base = os.path.splitext(os.path.basename(path))[0]
        dats = [x for x in listed[(repo, d)] if x['name'].endswith('.dat')][:12]
        needed = set(re.findall(r'(\w+)\s*(?:\[[^\]]*\])*\s*=\s*\.\.\.', text)) | set(re.findall(r'enum\s+(\w+)\s*\.\.\.', text))
        same = [x for x in dats if os.path.splitext(x['name'])[0] == base]
        if not same:
            # download candidates and keep the one defining most of the needed names
            best, best_n = None, 0
            for x in dats:
                ddest = os.path.join(files, repo.replace('/', '__'), d, x['name'])
                if not os.path.exists(ddest):
                    blob = gh(f"repos/{repo}/git/blobs/{x['sha']}")
                    if blob: open(ddest, 'wb').write(base64.b64decode(blob['content']))
                if not os.path.exists(ddest): continue
                names = set(re.findall(r'^\s*(\w+)\s*=', open(ddest, encoding='utf8', errors='replace').read(), re.M))
                k = len(names & needed)
                if k > best_n: best, best_n = x, k
            same = [best] if best else []
        for x in same:
            ddest = os.path.join(files, repo.replace('/', '__'), d, x['name'])
            if not os.path.exists(ddest):
                blob = gh(f"repos/{repo}/git/blobs/{x['sha']}")
                if blob: open(ddest, 'wb').write(base64.b64decode(blob['content']))
            if os.path.exists(ddest): entry['data'].append(ddest)
    manifest.append(entry)
json.dump(manifest, open(os.path.join(root, 'manifest.json'), 'w'), indent=1)
print(len(manifest), 'models,', sum(1 for m in manifest if m['data']), 'with data')
