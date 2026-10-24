// Small SVG charts for the playground: horizontal bars, a Gantt chart and a
// single stacked bar.  Colors come from CSS custom properties, so light and
// dark mode switch with the page.

const SVG = 'http://www.w3.org/2000/svg';
const SLOTS = ['--s1', '--s2', '--s3', '--s4', '--s5', '--s6', '--s7', '--s8'];

function el(name, attrs = {}, parent) {
  const e = document.createElementNS(SVG, name);
  for (const [k, v] of Object.entries(attrs)) e.setAttribute(k, v);
  if (parent) parent.appendChild(e);
  return e;
}

function text(parent, x, y, s, attrs = {}) {
  const t = el('text', { x, y, ...attrs }, parent);
  t.textContent = s;
  return t;
}

export function formatNumber(v) {
  if (!Number.isFinite(v)) return String(v);
  if (Number.isInteger(v)) return v.toLocaleString('en-US');
  const a = Math.abs(v);
  return v.toLocaleString('en-US', { maximumSignificantDigits: a >= 1000 ? 7 : 5 });
}

/** "Nice" tick values covering [lo, hi]. */
function ticks(lo, hi, count = 5) {
  if (hi === lo) hi = lo + 1;
  const raw = (hi - lo) / count;
  const mag = 10 ** Math.floor(Math.log10(raw));
  const step = [1, 2, 2.5, 5, 10].map((m) => m * mag).find((s) => s >= raw) ?? raw;
  const out = [];
  for (let v = Math.ceil(lo / step) * step; v <= hi + step * 1e-9; v += step) out.push(+v.toPrecision(12));
  return out;
}

/** Hover / focus tooltip for a mark. */
function tip(mark, html) {
  const box = document.getElementById('tooltip');
  mark.setAttribute('tabindex', '0');
  const show = (x, y) => {
    box.innerHTML = html;
    box.hidden = false;
    const w = box.offsetWidth;
    const h = box.offsetHeight;
    box.style.left = `${Math.min(x + 14, innerWidth - w - 8)}px`;
    box.style.top = `${Math.max(8, y - h - 10)}px`;
  };
  mark.addEventListener('pointermove', (e) => show(e.clientX, e.clientY));
  mark.addEventListener('pointerleave', () => (box.hidden = true));
  mark.addEventListener('focus', () => {
    const r = mark.getBoundingClientRect();
    show(r.left + r.width / 2, r.top);
  });
  mark.addEventListener('blur', () => (box.hidden = true));
}

const esc = (s) => String(s).replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' })[c]);

/** Width of a string in the 11px chart font, roughly. */
const textWidth = (s) => s.length * 6.2;

/**
 * Horizontal bars, one per variable (a single series: one color, no legend).
 * Values may be negative; the zero line is the baseline.
 */
export function barChart(container, rows, { width = 560 } = {}) {
  container.replaceChildren();
  const labelW = Math.min(220, Math.max(60, ...rows.map((r) => textWidth(r.name)))) + 8;
  const barH = 16;
  const gap = 6;
  const top = 22;
  const height = top + rows.length * (barH + gap) + 4;
  const lo = Math.min(0, ...rows.map((r) => r.value));
  const hi = Math.max(0, ...rows.map((r) => r.value));
  const ts = ticks(lo, hi);
  const min = Math.min(lo, ts[0]);
  const max = Math.max(hi, ts[ts.length - 1]);
  const plotL = labelW;
  const plotR = width - 12;
  const x = (v) => plotL + ((v - min) / (max - min || 1)) * (plotR - plotL);
  const svg = el('svg', { viewBox: `0 0 ${width} ${height}`, role: 'img', 'aria-label': `Bar chart of ${rows.length} variable values` }, container);
  for (const t of ts) {
    el('line', { x1: x(t), x2: x(t), y1: top - 6, y2: height - 4, class: t === 0 ? 'axis' : 'grid' }, svg);
    text(svg, x(t), 12, formatNumber(t), { 'text-anchor': 'middle' });
  }
  let maxRow = rows[0];
  for (const r of rows) if (Math.abs(r.value) > Math.abs(maxRow.value)) maxRow = r;
  rows.forEach((r, i) => {
    const y = top + i * (barH + gap);
    text(svg, labelW - 8, y + barH / 2 + 4, r.name.length > 34 ? r.name.slice(0, 33) + '…' : r.name, { 'text-anchor': 'end' });
    const x0 = x(Math.min(0, r.value));
    const x1 = x(Math.max(0, r.value));
    const w = Math.max(1, x1 - x0);
    // Rounded at the data end, square at the baseline.
    const rr = Math.min(4, w / 2);
    const d = r.value >= 0
      ? `M${x0},${y} H${x0 + w - rr} Q${x0 + w},${y} ${x0 + w},${y + rr} V${y + barH - rr} Q${x0 + w},${y + barH} ${x0 + w - rr},${y + barH} H${x0} Z`
      : `M${x1},${y} H${x0 + rr} Q${x0},${y} ${x0},${y + rr} V${y + barH - rr} Q${x0},${y + barH} ${x0 + rr},${y + barH} H${x1} Z`;
    const bar = el('path', { d, fill: 'var(--s1)', class: 'mark' }, svg);
    tip(bar, `<strong>${esc(r.name)}</strong>${formatNumber(r.value)}`);
    if (r === maxRow) {
      const lx = r.value >= 0 ? x1 + 6 : x0 - 6;
      const anchor = r.value >= 0 ? 'start' : 'end';
      const fits = r.value >= 0 ? lx + textWidth(formatNumber(r.value)) < width : lx - textWidth(formatNumber(r.value)) > plotL;
      if (fits) text(svg, lx, y + barH / 2 + 4, formatNumber(r.value), { 'text-anchor': anchor, class: 'label-strong' });
    }
  });
}

/** The job of an activity: task[j][s] -> task[j]; task[x] -> task. */
function groupOf(name) {
  const indices = name.match(/\[[^\]]*\]/g) ?? [];
  return indices.length >= 2 ? name.slice(0, name.lastIndexOf('[')) : name.replace(/\[.*$/, '');
}

/** Text color for a label on a fill: near-black on light fills, white on dark ones. */
function inkOn(cssVar) {
  const v = getComputedStyle(document.documentElement).getPropertyValue(cssVar).trim();
  const m = /^#([0-9a-f]{6})$/i.exec(v);
  if (!m) return '#fff';
  const lin = (c) => (c <= 0.04045 ? c / 12.92 : ((c + 0.055) / 1.055) ** 2.4);
  const [r, g, b] = [0, 2, 4].map((i) => lin(parseInt(m[1].slice(i, i + 2), 16) / 255));
  const lum = 0.2126 * r + 0.7152 * g + 0.0722 * b;
  return (lum + 0.05) / 0.05 > 1.05 / (lum + 0.05) ? '#0b0b0b' : '#ffffff';
}

function resourceLabel(r) {
  const m = /^(noOverlap|cumul)#(\d+)$/.exec(r);
  return m ? `${m[1] === 'cumul' ? 'cumul function' : 'noOverlap'} ${m[2]}` : r;
}

/** Bars of one row in lanes, so that overlapping bars (a discrete resource) do not hide each other. */
function lanes(acts) {
  const out = [];
  for (const a of [...acts].sort((p, q) => p.start - q.start || p.end - q.end)) {
    const lane = out.find((l) => l[l.length - 1].end <= a.start);
    if (lane) lane.push(a);
    else out.push([a]);
  }
  return out;
}

/**
 * Gantt chart: one row per resource (or per activity when activities use no
 * resource), split into lanes where its activities overlap, bars colored by
 * job when there are 2..8 jobs.
 */
export function gantt(container, activities, { width = 560 } = {}) {
  container.replaceChildren();
  const byRow = new Map();
  for (const a of activities) {
    const rows = a.resources.length ? a.resources : [a.name];
    for (const r of rows) {
      if (!byRow.has(r)) byRow.set(r, []);
      byRow.get(r).push(a);
    }
  }
  const collator = new Intl.Collator('en', { numeric: true });
  const rowNames = [...byRow.keys()].sort(collator.compare);
  const rows = rowNames.flatMap((r) => lanes(byRow.get(r)).map((acts, k) => ({ r, acts, first: k === 0 })));
  const groups = [...new Set(activities.map((a) => groupOf(a.name)))].sort(collator.compare);
  const colored = groups.length >= 2 && groups.length <= 8;
  const slotOf = (a) => (colored ? SLOTS[groups.indexOf(groupOf(a.name))] : '--s1');
  const color = (a) => `var(${slotOf(a)})`;

  if (colored) {
    const legend = document.createElement('ul');
    legend.className = 'legend';
    groups.forEach((g, i) => {
      const li = document.createElement('li');
      li.innerHTML = `<span class="key" style="background: var(${SLOTS[i]})"></span>${esc(g)}`;
      legend.appendChild(li);
    });
    container.appendChild(legend);
  }

  const labelW = Math.min(170, Math.max(50, ...rowNames.map((r) => textWidth(resourceLabel(r))))) + 10;
  const rowH = 26;
  const barH = 18;
  const top = 22;
  const height = top + rows.length * rowH + 6;
  const end = Math.max(1, ...activities.map((a) => a.end));
  const start = Math.min(0, ...activities.map((a) => a.start));
  const ts = ticks(start, end, 6);
  const max = Math.max(end, ts[ts.length - 1]);
  const plotL = labelW;
  const plotR = width - 12;
  const x = (v) => plotL + ((v - start) / (max - start || 1)) * (plotR - plotL);
  const svg = el('svg', { viewBox: `0 0 ${width} ${height}`, role: 'img', 'aria-label': `Schedule of ${activities.length} activities on ${rowNames.length} rows` }, container);
  for (const t of ts) {
    el('line', { x1: x(t), x2: x(t), y1: top - 6, y2: height - 4, class: t === start ? 'axis' : 'grid' }, svg);
    text(svg, x(t), 12, formatNumber(t), { 'text-anchor': 'middle' });
  }
  rows.forEach(({ r, acts, first }, i) => {
    const y = top + i * rowH + (rowH - barH) / 2;
    if (first) text(svg, labelW - 10, y + barH / 2 + 4, resourceLabel(r), { 'text-anchor': 'end' });
    for (const a of acts) {
      // A 2px surface gap between abutting bars.
      const x0 = x(a.start) + 1;
      const w = Math.max(2, x(a.end) - x(a.start) - 2);
      const bar = el('rect', { x: x0, y, width: w, height: barH, rx: Math.min(4, w / 2), fill: color(a), class: 'mark' }, svg);
      const where = a.resources.length ? ` on ${esc(a.resources.map(resourceLabel).join(', '))}` : '';
      tip(bar, `<strong>${esc(a.name)}</strong>${formatNumber(a.start)} → ${formatNumber(a.end)} (${formatNumber(a.end - a.start)})${where}`);
      const label = a.name.replace(/^.*?\[/, '[');
      const short = a.name.length * 6.2 + 8 < w ? a.name : textWidth(label) + 8 < w ? label : '';
      if (short) text(svg, x0 + 5, y + barH / 2 + 4, short, { class: 'inside', style: `fill: ${inkOn(slotOf(a))}` });
    }
  });
  const note = document.createElement('p');
  note.className = 'chart-note';
  note.textContent = `The schedule ends at ${formatNumber(end)}. Hover a bar for its times.`;
  container.appendChild(note);
}

/** One stacked bar of parts of a whole, with a legend that carries the values. */
export function stackedBar(container, parts, { width = 900 } = {}) {
  container.replaceChildren();
  const legend = document.createElement('ul');
  legend.className = 'legend';
  for (const p of parts) {
    const li = document.createElement('li');
    li.innerHTML = `<span class="key" style="background: ${p.color}"></span>${p.icon ? `<span aria-hidden="true">${p.icon}</span>` : ''}${esc(p.label)} <span class="value">${p.value}</span>`;
    legend.appendChild(li);
  }
  container.appendChild(legend);
  const total = parts.reduce((s, p) => s + p.value, 0);
  const h = 26;
  const svg = el('svg', { viewBox: `0 0 ${width} ${h}`, role: 'img', 'aria-label': parts.map((p) => `${p.label}: ${p.value}`).join(', ') }, container);
  let at = 0;
  parts.forEach((p, i) => {
    const w = (p.value / total) * width;
    const x0 = at + (i > 0 ? 1 : 0);
    const ww = Math.max(1, w - (i > 0 ? 1 : 0) - (i < parts.length - 1 ? 1 : 0));
    const rect = el('rect', { x: x0, y: 0, width: ww, height: h, rx: i === 0 || i === parts.length - 1 ? 4 : 0, fill: p.color, class: 'mark' }, svg);
    tip(rect, `<strong>${esc(p.label)}</strong>${p.value} of ${total} (${Math.round((p.value / total) * 100)}%)`);
    if (ww > 44) text(svg, x0 + 8, h / 2 + 4, String(p.value), { class: 'inside', style: `fill: ${p.ink ?? '#fff'}` });
    at += w;
  });
}
