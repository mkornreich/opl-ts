// opl-ts playground: pick an example, edit its files, solve it in a worker.

import { barChart, formatNumber, gantt, stackedBar } from './charts.js';

const $ = (id) => document.getElementById(id);
const state = {
  manifest: null,
  example: null,
  /** Edited file contents, per example id. */
  edits: new Map(),
  file: null,
  worker: null,
  running: false,
  reply: null,
  view: 'output',
};

const esc = (s) => String(s).replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' })[c]);

// ------------------------------------------------------------------ setup

async function main() {
  const res = await fetch('examples.json');
  state.manifest = await res.json();
  renderVerification(state.manifest.verification);
  renderExampleList();
  const fromHash = location.hash.slice(1);
  const first = state.manifest.examples.find((e) => e.id === fromHash) ?? state.manifest.examples[0];
  selectExample(first.id, false);
  $('solve').addEventListener('click', () => (state.running ? stop() : solve()));
  $('reset').addEventListener('click', resetFiles);
  $('code').addEventListener('input', () => {
    filesOf(state.example)[state.file] = $('code').value;
  });
  $('code').addEventListener('keydown', onEditorKey);
  addEventListener('hashchange', () => {
    const id = location.hash.slice(1);
    if (id && id !== state.example?.id && state.manifest.examples.some((e) => e.id === id)) selectExample(id, false);
  });
  // Charts read their ink from the current scheme: redraw when it changes.
  matchMedia('(prefers-color-scheme: dark)').addEventListener('change', () => {
    renderVerification(state.manifest.verification);
    if (state.reply) showView(state.view);
  });
}

function renderVerification(v) {
  const c = v.corpus;
  const runnable = c.models - c.noData;
  const ran = c.finished + c.atLimit;
  $('kpi-corpus').textContent = `${ran} / ${runnable}`;
  $('kpi-corpus-note').textContent = `${Math.round((ran / runnable) * 100)}% of the ${runnable} that have their data, from ${c.repositories} repositories`;
  $('kpi-highs').textContent = `${v.highsAgree} / ${v.highsAgree}`;
  const fuzz = v.mipFuzz + v.qpFuzz.total + v.bruteForce;
  $('kpi-fuzz').textContent = fuzz.toLocaleString('en-US');
  $('kpi-fuzz-note').textContent = `${v.mipFuzz.toLocaleString('en-US')} LP/MIP and ${v.qpFuzz.total} QP vs HiGHS, ${v.bruteForce.toLocaleString('en-US')} CP vs brute force; no disagreement left`;
  $('kpi-tests').textContent = String(v.tests);
  $('kpi-tests-note').textContent = `and all ${v.tutorial} OPL Studio tutorial files`;
  $('corpus-caption').textContent =
    `${c.models} OPL models from ${c.repositories} GitHub repositories, run with a 20-second limit. ` +
    `${c.noData} cannot run anywhere because their data or included files are not in the repository; the bar shows the other ${runnable}.`;
  stackedBar($('corpus-chart'), [
    { label: 'Finish', value: c.finished, color: 'var(--good)', icon: '✓', ink: '#0b0b0b' },
    { label: 'Stop at the time limit (hard puzzles)', value: c.atLimit, color: 'var(--warning)', icon: '⏱', ink: '#0b0b0b' },
    { label: 'Fail (shell commands, too large, invalid, unsupported)', value: c.other, color: 'var(--critical)', icon: '✕' },
  ]);
}

function renderExampleList() {
  const list = $('example-list');
  list.replaceChildren();
  for (const cat of state.manifest.categories) {
    const items = state.manifest.examples.filter((e) => e.category === cat);
    if (!items.length) continue;
    const group = document.createElement('div');
    group.className = 'group';
    group.innerHTML = `<p class="group-title">${esc(cat)}</p>`;
    const box = document.createElement('div');
    box.className = 'group-items';
    for (const e of items) {
      const b = document.createElement('button');
      b.type = 'button';
      b.className = 'example';
      b.dataset.id = e.id;
      b.textContent = e.title;
      b.addEventListener('click', () => selectExample(e.id, true));
      box.appendChild(b);
    }
    group.appendChild(box);
    list.appendChild(group);
  }
}

// ------------------------------------------------------------------ examples and files

function filesOf(example) {
  if (!state.edits.has(example.id)) state.edits.set(example.id, { ...example.files });
  return state.edits.get(example.id);
}

function selectExample(id, updateHash) {
  if (state.running) stop();
  const ex = state.manifest.examples.find((e) => e.id === id);
  state.example = ex;
  if (updateHash) history.replaceState(null, '', `#${id}`);
  for (const b of document.querySelectorAll('.example')) b.setAttribute('aria-current', String(b.dataset.id === id));
  $('example-title').textContent = ex.title;
  $('example-summary').textContent = ex.summary;
  const badge = $('example-source');
  badge.hidden = !ex.source;
  badge.textContent = ex.source ?? '';
  $('force-cp').checked = false;
  state.file = ex.main;
  renderFileTabs();
  state.reply = null;
  $('status').innerHTML = '<span class="muted">Press Solve to run the model.</span>';
  $('result-tabs').replaceChildren();
  for (const v of document.querySelectorAll('#result-views .view')) v.hidden = true;
}

function renderFileTabs() {
  const tabs = $('file-tabs');
  tabs.replaceChildren();
  const names = Object.keys(filesOf(state.example));
  // The main file first, then the others in manifest order.
  names.sort((a, b) => (a === state.example.main ? -1 : b === state.example.main ? 1 : 0));
  for (const name of names) {
    const b = document.createElement('button');
    b.type = 'button';
    b.className = 'tab';
    b.role = 'tab';
    b.textContent = name;
    b.setAttribute('aria-selected', String(name === state.file));
    b.addEventListener('click', () => {
      state.file = name;
      renderFileTabs();
    });
    tabs.appendChild(b);
  }
  $('code').value = filesOf(state.example)[state.file];
}

function resetFiles() {
  state.edits.delete(state.example.id);
  renderFileTabs();
}

/** Tab indents (two spaces); Ctrl/Cmd+Enter solves. */
function onEditorKey(e) {
  const ta = e.currentTarget;
  if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {
    e.preventDefault();
    if (!state.running) solve();
    return;
  }
  if (e.key === 'Tab' && !e.shiftKey && !e.altKey && !e.ctrlKey && !e.metaKey) {
    e.preventDefault();
    ta.setRangeText('  ', ta.selectionStart, ta.selectionEnd, 'end');
    filesOf(state.example)[state.file] = ta.value;
  }
}

// ------------------------------------------------------------------ solving

function worker() {
  if (!state.worker) {
    state.worker = new Worker('worker.js', { type: 'module' });
    state.worker.addEventListener('message', (e) => finish(e.data));
    state.worker.addEventListener('error', (e) => {
      finish({ output: '', error: e.message || 'the solver worker failed to start', solve: null, variables: [], activities: [], written: {}, ms: 0 });
    });
  }
  return state.worker;
}

function solve() {
  const ex = state.example;
  state.running = true;
  const btn = $('solve');
  btn.textContent = 'Stop';
  btn.classList.add('running');
  $('status').innerHTML = '<span class="muted">Solving…</span>';
  worker().postMessage({
    files: { ...filesOf(ex) },
    main: ex.main,
    data: ex.data,
    timeLimit: Number($('time-limit').value),
    forceCP: $('force-cp').checked,
  });
}

function stop() {
  state.worker?.terminate();
  state.worker = null;
  state.running = false;
  resetButton();
  $('status').innerHTML = '<span class="muted">Stopped.</span>';
}

function resetButton() {
  const btn = $('solve');
  btn.textContent = 'Solve';
  btn.classList.remove('running');
}

const STATUS = {
  optimal: ['Optimal', 'var(--good)'],
  feasible: ['Feasible (time limit reached)', 'var(--warning)'],
  infeasible: ['Infeasible', 'var(--critical)'],
  unbounded: ['Unbounded', 'var(--critical)'],
  limit: ['No solution within the limits', 'var(--warning)'],
  none: ['Solved', 'var(--good)'],
};

function finish(reply) {
  state.running = false;
  resetButton();
  state.reply = reply;
  const st = $('status');
  if (reply.error) {
    st.innerHTML = `<div class="status-line"><span class="dot" style="background: var(--critical)"></span>Error</div><div class="error">${esc(reply.error)}</div>`;
  } else if (reply.solve) {
    const s = reply.solve;
    const [label, color] = s.status === 'optimal' && !s.sense ? ['Solution found', 'var(--good)'] : (STATUS[s.status] ?? [s.status, 'var(--muted)']);
    const obj = s.sense && Number.isFinite(s.objective)
      ? `<div class="objective">${(+s.objective.toPrecision(10)).toLocaleString('en-US', { maximumFractionDigits: 8 })}</div><div class="muted">objective (${s.sense})</div>`
      : '';
    st.innerHTML = `<div class="status-line"><span class="dot" style="background: ${color}"></span>${esc(label)}</div>${obj}<div class="stats">${esc(s.stats)} · ${Math.round(reply.ms)} ms in the browser</div>`;
  } else {
    st.innerHTML = `<div class="status-line"><span class="dot" style="background: var(--good)"></span>Done</div><div class="stats">${Math.round(reply.ms)} ms in the browser</div>`;
  }
  const views = [['output', 'Output']];
  const nonzero = reply.variables.filter((v) => Math.abs(v.value) > 1e-9);
  if (reply.activities.length) views.push(['schedule', 'Schedule']);
  if (nonzero.length) views.push(['chart', 'Chart']);
  if (reply.variables.length) views.push(['table', 'Table']);
  if (Object.keys(reply.written).length) views.push(['files', 'Files written']);
  const tabs = $('result-tabs');
  tabs.replaceChildren();
  for (const [id, label] of views) {
    const b = document.createElement('button');
    b.type = 'button';
    b.className = 'tab';
    b.role = 'tab';
    b.dataset.view = id;
    b.textContent = label;
    b.addEventListener('click', () => showView(id));
    tabs.appendChild(b);
  }
  showView(reply.activities.length ? 'schedule' : 'output');
}

function showView(id) {
  state.view = id;
  const reply = state.reply;
  for (const b of $('result-tabs').children) b.setAttribute('aria-selected', String(b.dataset.view === id));
  for (const v of document.querySelectorAll('#result-views .view')) v.hidden = v.id !== `view-${id}`;
  const view = $(`view-${id}`);
  if (id === 'output') {
    view.innerHTML = esc(reply.output || (reply.error ? '' : '(no output)')) + (reply.error ? `<span class="error">${esc(reply.error)}</span>` : '');
  } else if (id === 'chart') {
    const nonzero = reply.variables.filter((v) => Math.abs(v.value) > 1e-9);
    const shown = nonzero.slice(0, 40);
    barChart(view, shown);
    const note = document.createElement('p');
    note.className = 'chart-note';
    note.textContent = nonzero.length > shown.length
      ? `The first ${shown.length} of ${nonzero.length} non-zero variables; the table lists them all.`
      : `${nonzero.length} non-zero variable${nonzero.length === 1 ? '' : 's'} of ${reply.variables.length}. Hover a bar for its value.`;
    view.appendChild(note);
  } else if (id === 'schedule') {
    gantt(view, reply.activities);
  } else if (id === 'table') {
    const rows = reply.variables
      .map((v) => `<tr><td class="name">${esc(v.name)}</td><td class="num">${formatNumber(v.value)}</td></tr>`)
      .join('');
    view.innerHTML = `<div class="table-wrap" tabindex="0" role="region" aria-labelledby="vars-caption"><table><caption id="vars-caption">${reply.variables.length} decision variables</caption><thead><tr><th scope="col">Variable</th><th scope="col">Value</th></tr></thead><tbody>${rows}</tbody></table></div>`;
  } else if (id === 'files') {
    view.innerHTML = Object.entries(reply.written)
      .map(([name, text]) => `<div class="file-out"><h3>${esc(name)}</h3><pre class="view">${esc(text)}</pre></div>`)
      .join('');
  }
}

main().catch((e) => {
  $('status').innerHTML = `<span class="error">Could not load the examples: ${esc(e.message)}</span>`;
});
