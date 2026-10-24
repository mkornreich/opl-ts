/**
 * Builds the GitHub Pages site into site/: the solver bundled for a web
 * worker (Node modules replaced by the shims in web/shims), the page, and the
 * examples with their file contents.
 *
 * usage: node scripts/build-web.mjs [out-dir]
 */

import * as esbuild from 'esbuild';
import * as fs from 'node:fs';
import * as path from 'node:path';
import { fileURLToPath } from 'node:url';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const out = path.resolve(process.argv[2] ?? path.join(root, 'site'));
const shim = (f) => path.join(root, 'web', 'shims', f);

fs.rmSync(out, { recursive: true, force: true });
fs.mkdirSync(out, { recursive: true });

await esbuild.build({
  entryPoints: [path.join(root, 'web', 'worker.ts')],
  outfile: path.join(out, 'worker.js'),
  bundle: true,
  format: 'esm',
  platform: 'browser',
  target: 'es2022',
  minify: true,
  sourcemap: true,
  legalComments: 'none',
  inject: [shim('process.ts')],
  alias: {
    'node:fs': shim('fs.ts'),
    'node:path': shim('path.ts'),
    'node:vm': shim('vm.ts'),
    'node:child_process': shim('unavailable.ts'),
    'node:module': shim('unavailable.ts'),
    xlsx: shim('unavailable.ts'),
  },
  logLevel: 'warning',
});

for (const f of ['index.html', 'style.css', 'app.js', 'charts.js']) {
  fs.copyFileSync(path.join(root, 'web', f), path.join(out, f));
}
fs.writeFileSync(path.join(out, '.nojekyll'), '');

// Examples: the manifest plus the text of every file.
const manifest = JSON.parse(fs.readFileSync(path.join(root, 'web', 'examples', 'manifest.json'), 'utf8'));
for (const ex of manifest.examples) {
  ex.files = Object.fromEntries(ex.files.map((f) => [path.basename(f), fs.readFileSync(path.join(root, f), 'utf8')]));
}
fs.writeFileSync(path.join(out, 'examples.json'), JSON.stringify(manifest));

const kb = (f) => `${Math.round(fs.statSync(path.join(out, f)).size / 1024)} KB`;
console.log(`site built in ${path.relative(root, out) || '.'}: worker.js ${kb('worker.js')}, examples.json ${kb('examples.json')}`);
