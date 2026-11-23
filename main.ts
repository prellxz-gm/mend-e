// mend — one patch tool for every AI edit format.
// Implements SPEC.md v1: unified diffs, SEARCH/REPLACE blocks, V4A patches
// and JSON editor calls, with three-tier fuzzy matching, exact stdout/exit
// codes, and all-or-nothing writes. Node stdlib only, deterministic.

import { mkdirSync, readFileSync, unlinkSync, writeFileSync, writeSync } from 'node:fs';
import { dirname, join } from 'node:path';

type Brk = '\n' | '\r\n';

interface FileModel {
  lines: string[];
  brk: Brk;
  fin: boolean;
}

interface Fail {
  code: string;
  path: string;
}

class ParseErr extends Error {
  line: number;
  constructor(line: number) {
    super(`parse ${line}`);
    this.line = line;
  }
}

function fail(code: string, path: string): Fail {
  return { code, path };
}

function isSafe(p: string): boolean {
  if (p === '') return false;
  if (p.startsWith('/')) return false;
  if (p.includes('\\')) return false;
  for (const s of p.split('/')) {
    if (s === '' || s === '.' || s === '..') return false;
  }
  return true;
}

function parseFile(text: string): FileModel {
  let brk: Brk = '\n';
  const ni = text.indexOf('\n');
  if (ni > 0 && text[ni - 1] === '\r') brk = '\r\n';
  if (text === '') return { lines: [], brk, fin: false };
  const parts = text.split(brk);
  let fin = false;
  if (text.endsWith(brk)) {
    fin = true;
    parts.pop();
  }
  return { lines: parts, brk, fin };
}

function serFile(m: FileModel): string {
  if (m.lines.length === 0) return '';
  return m.lines.join(m.brk) + (m.fin ? m.brk : '');
}

// Patch lines: split at \n, one trailing \r removed per line, no empty
// piece after a final \n.
function patchLines(text: string): string[] {
  const parts = text.split('\n');
  if (text.endsWith('\n')) parts.pop();
  return parts.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function leadingWs(s: string): string {
  const m = /^[ \t]*/.exec(s);
  return m ? m[0] : '';
}

function normLine(s: string, tier: number): string {
  if (tier === 0) return s;
  if (tier === 1) return s.replace(/[ \t]+$/, '');
  return s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

// First tier (0, then 1, then 2; strict: 0 only) at which O occurs in
// lines at or after `from`, with every occurrence position (overlap ok).
function findTierFrom(
  lines: string[],
  o: string[],
  from: number,
  strict: boolean,
): { tier: number; pos: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const no = o.map((x) => normLine(x, t));
    const pos: number[] = [];
    for (let i = from; i + o.length <= lines.length; i++) {
      let ok = true;
      for (let j = 0; j < o.length; j++) {
        if (normLine(lines[i + j], t) !== no[j]) {
          ok = false;
          break;
        }
      }
      if (ok) pos.push(i);
    }
    if (pos.length > 0) return { tier: t, pos };
  }
  return null;
}

function findTier(lines: string[], o: string[], strict: boolean): { tier: number; pos: number[] } | null {
  return findTierFrom(lines, o, 0, strict);
}

// Single-line anchor search: first line at/after `from` equal to the
// anchor at the first tier where one exists.
function findAnchor(lines: string[], anchor: string, from: number, strict: boolean): number {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const na = normLine(anchor, t);
    for (let i = from; i < lines.length; i++) {
      if (normLine(lines[i], t) === na) return i;
    }
  }
  return -1;
}

// Build the replacement lines for a matched O. `items` are N's lines in
// order; context items take the file's own matched line, other lines are
// written as they are (tier 2: re-indented with F/P).
function buildNew(
  o: string[],
  items: Array<{ ctx: boolean; text: string; oi?: number }>,
  fileLines: string[],
  at: number,
  tier: number,
): string[] {
  const out: string[] = [];
  let f = '';
  let p = '';
  if (tier === 2 && o.length > 0) {
    f = leadingWs(fileLines[at]);
    p = leadingWs(o[0]);
  }
  for (const it of items) {
    if (it.ctx) {
      // A context line is the file's own matched line: its index in O
      // counts the '-' lines that sit between context lines.
      out.push(fileLines[at + (it.oi ?? 0)]);
    } else if (tier === 2) {
      const s = it.text;
      if (s !== '' && s.trim() !== '' && s.startsWith(p)) out.push(f + s.slice(p.length));
      else out.push(s);
    } else {
      out.push(it.text);
    }
  }
  return out;
}

// Same, for formats with plain N lines (no context lines).
function buildNewPlain(o: string[], nLines: string[], fileLines: string[], at: number, tier: number): string[] {
  return buildNew(
    o,
    nLines.map((t) => ({ ctx: false, text: t })),
    fileLines,
    at,
    tier,
  );
}

function countOcc(hay: string, needle: string): number {
  let c = 0;
  let i = hay.indexOf(needle);
  while (i >= 0) {
    c++;
    i = hay.indexOf(needle, i + 1);
  }
  return c;
}

// In-memory tree: current contents (null = absent) plus the initial
// contents of every path ever looked at, for the exit-0 listing.
class Tree {
  cur = new Map<string, string | null>();
  init = new Map<string, string | null>();
  touched = new Set<string>();
  moves: Array<{ old: string; nw: string }> = [];

  get(p: string): string | null {
    if (!this.cur.has(p)) {
      let v: string | null = null;
      try {
        v = readFileSync(join(process.cwd(), ...p.split('/')), 'utf8');
      } catch {
        v = null;
      }
      this.cur.set(p, v);
      this.init.set(p, v);
    }
    const v = this.cur.get(p);
    return v === undefined ? null : v;
  }

  set(p: string, v: string | null): void {
    this.get(p);
    this.cur.set(p, v);
    this.touched.add(p);
  }
}

function detectFormat(lines: string[]): string | null {
  let firstNB: string | undefined;
  for (const l of lines) {
    if (l.trim() !== '') {
      firstNB = l;
      break;
    }
  }
  if (firstNB !== undefined) {
    if (firstNB.trim() === '*** Begin Patch') return 'v4a';
    const c = firstNB.trimStart()[0];
    if (c === '[' || c === '{') return 'json';
  }
  for (const l of lines) {
    if (l.trimEnd() === '<<<<<<< SEARCH') return 'search-replace';
  }
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].startsWith('diff --git ')) return 'unified';
    if (lines[i].startsWith('--- ') && i + 1 < lines.length && lines[i + 1].startsWith('+++ ')) return 'unified';
  }
  return null;
}

function usage(): { code: number; out: string[] } {
  return { code: 2, out: ['error: usage'] };
}

// ---- Unified diffs (SPEC section 6) ----

interface Hunk {
  a: number;
  body: string[];
}

interface UniSection {
  diffOld: string | undefined;
  diffNew: string | undefined;
  oldPath: string | undefined;
  oldNull: boolean;
  newPath: string | undefined;
  newNull: boolean;
  renameFrom: string | undefined;
  renameTo: string | undefined;
  isCreate: boolean;
  isDelete: boolean;
  hunks: Hunk[];
}

function headerPath(line: string): string | null {
  let t = line.slice(4);
  const tab = t.indexOf('\t');
  if (tab >= 0) t = t.slice(0, tab);
  t = t.trim();
  if (t === '/dev/null') return null;
  if (t.startsWith('a/')) t = t.slice(2);
  else if (t.startsWith('b/')) t = t.slice(2);
  return t;
}

function parseUnified(lines: string[]): UniSection[] {
  const sections: UniSection[] = [];
  let cur: UniSection | null = null;
  let header = false;
  let i = 0;
  const n = lines.length;
  const fresh = (dOld: string | undefined, dNew: string | undefined): UniSection => ({
    diffOld: dOld,
    diffNew: dNew,
    oldPath: undefined,
    oldNull: false,
    newPath: undefined,
    newNull: false,
    renameFrom: undefined,
    renameTo: undefined,
    isCreate: false,
    isDelete: false,
    hunks: [],
  });
  while (i < n) {
    const line = lines[i];
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/(\S+) b\/(\S+)$/.exec(line);
      if (!m) throw new ParseErr(i + 1);
      cur = fresh(m[1], m[2]);
      sections.push(cur);
      header = true;
      i++;
      continue;
    }
    if (line.startsWith('@@')) {
      if (!cur) throw new ParseErr(i + 1);
      const hm = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/.exec(line);
      if (!hm) throw new ParseErr(i + 1);
      header = false;
      const body: string[] = [];
      i++;
      while (i < n) {
        const b = lines[i];
        if (b.startsWith('diff --git ')) break;
        if (b.startsWith('--- ') && i + 1 < n && lines[i + 1].startsWith('+++ ')) break;
        if (b === '' || b[0] === ' ' || b[0] === '-' || b[0] === '+' || b[0] === '\\') {
          body.push(b);
          i++;
          continue;
        }
        break;
      }
      while (body.length > 0 && body[body.length - 1] === '') body.pop();
      cur.hunks.push({ a: parseInt(hm[1], 10), body });
      continue;
    }
    if (cur && header) {
      if (line.startsWith('--- ')) {
        if (i + 1 >= n || !lines[i + 1].startsWith('+++ ')) throw new ParseErr(i + 2);
        // The first ---/+++ pair names the paths; a later pair in the
        // same header does not rename them.
        if (cur.oldPath === undefined && !cur.oldNull) {
          const p = headerPath(line);
          if (p === null) cur.oldNull = true;
          else cur.oldPath = p;
        }
        i++;
        continue;
      }
      if (line.startsWith('+++ ')) {
        if (cur.newPath === undefined && !cur.newNull) {
          const p = headerPath(line);
          if (p === null) cur.newNull = true;
          else cur.newPath = p;
        }
        i++;
        continue;
      }
      if (line.startsWith('rename from ')) {
        cur.renameFrom = line.slice('rename from '.length).trim();
        i++;
        continue;
      }
      if (line.startsWith('rename to ')) {
        cur.renameTo = line.slice('rename to '.length).trim();
        i++;
        continue;
      }
      if (line.startsWith('new file mode')) {
        cur.isCreate = true;
        i++;
        continue;
      }
      if (line.startsWith('deleted file mode')) {
        cur.isDelete = true;
        i++;
        continue;
      }
      i++;
      continue;
    }
    if (line.startsWith('--- ') && i + 1 < n && lines[i + 1].startsWith('+++ ')) {
      cur = fresh(undefined, undefined);
      sections.push(cur);
      header = true;
      continue;
    }
    i++;
  }
  return sections;
}

// Split a hunk body into O lines and N items (context items flagged,
// each carrying its index inside O so '-' lines between context lines
// are counted).
function splitHunkBody(body: string[]): { o: string[]; nItems: Array<{ ctx: boolean; text: string; oi?: number }> } {
  const o: string[] = [];
  const nItems: Array<{ ctx: boolean; text: string; oi?: number }> = [];
  for (const b of body) {
    if (b === '') {
      o.push('');
      nItems.push({ ctx: true, text: '', oi: o.length - 1 });
    } else if (b[0] === ' ') {
      const t = b.slice(1);
      o.push(t);
      nItems.push({ ctx: true, text: t, oi: o.length - 1 });
    } else if (b[0] === '-') {
      o.push(b.slice(1));
    } else if (b[0] === '+') {
      nItems.push({ ctx: false, text: b.slice(1) });
    }
    // '\' lines are not part of O or N.
  }
  return { o, nItems };
}

// True when a '\' line follows the hunk's last context or '+' body line.
function hunkNoEol(body: string[]): boolean {
  let last = -1;
  for (let j = 0; j < body.length; j++) {
    const b = body[j];
    if (b === '' || b[0] === ' ' || b[0] === '+') last = j;
  }
  if (last < 0) return false;
  return last + 1 < body.length && body[last + 1][0] === '\\';
}

function applyHunks(
  model: FileModel,
  hunks: Hunk[],
  strict: boolean,
  path: string,
): { model: FileModel } | Fail {
  let lines = [...model.lines];
  let fin = model.fin;
  const brk = model.brk;
  let d = 0;
  for (const h of hunks) {
    const { o, nItems } = splitHunkBody(h.body);
    if (o.length === 0) {
      const pos = Math.min(h.a + d, lines.length);
      const atEnd = pos === lines.length;
      const newLines = nItems.map((x) => x.text);
      lines.splice(pos, 0, ...newLines);
      if (atEnd) fin = !hunkNoEol(h.body);
      d += newLines.length;
      continue;
    }
    const f = findTier(lines, o, strict);
    if (!f) return fail('no-match', path);
    const target = h.a - 1 + d;
    let best = f.pos[0];
    let bestDist = Math.abs(best - target);
    for (const p of f.pos) {
      const dist = Math.abs(p - target);
      if (dist < bestDist) {
        best = p;
        bestDist = dist;
      }
    }
    const at = best;
    const toEnd = at + o.length === lines.length;
    const repl = buildNew(o, nItems, lines, at, f.tier);
    lines.splice(at, o.length, ...repl);
    if (toEnd) fin = !hunkNoEol(h.body);
    d += repl.length - o.length;
  }
  return { model: { lines, brk, fin } };
}

function uniPaths(sec: UniSection): { oldP: string | null; newP: string | null } {
  let oldP: string | null | undefined;
  let newP: string | null | undefined;
  if (sec.oldPath !== undefined || sec.oldNull) oldP = sec.oldNull ? null : sec.oldPath ?? null;
  else if (sec.renameFrom !== undefined) oldP = sec.renameFrom;
  else oldP = sec.diffOld ?? null;
  if (sec.newPath !== undefined || sec.newNull) newP = sec.newNull ? null : sec.newPath ?? null;
  else if (sec.renameTo !== undefined) newP = sec.renameTo;
  else newP = sec.diffNew ?? null;
  return { oldP: oldP ?? null, newP: newP ?? null };
}

function applyUnified(tree: Tree, sec: UniSection, strict: boolean): Fail | null {
  const { oldP, newP } = uniPaths(sec);
  const isCreate = sec.isCreate || oldP === null;
  const isDelete = !isCreate && (sec.isDelete || newP === null);
  if (oldP !== null && !isSafe(oldP)) return fail('unsafe', oldP);
  if (newP !== null && !isSafe(newP)) return fail('unsafe', newP);
  if (isCreate) {
    const np = newP as string;
    if (tree.get(np) !== null) return fail('exists', np);
    const plus: string[] = [];
    for (const h of sec.hunks) {
      for (const b of h.body) {
        if (b[0] === '+') plus.push(b.slice(1));
      }
    }
    let fin = false;
    if (plus.length > 0) {
      fin = true;
      let lastHunk: Hunk | undefined;
      for (const h of sec.hunks) {
        if (h.body.some((b) => b[0] === '+')) lastHunk = h;
      }
      if (lastHunk) {
        // A '\' line follows the created file's last '+' line.
        let lastPlus = -1;
        for (let j = 0; j < lastHunk.body.length; j++) {
          if (lastHunk.body[j][0] === '+') lastPlus = j;
        }
        if (lastPlus >= 0 && lastPlus + 1 < lastHunk.body.length && lastHunk.body[lastPlus + 1][0] === '\\') {
          fin = false;
        }
      }
    }
    tree.set(np, serFile({ lines: plus, brk: '\n', fin }));
    return null;
  }
  if (isDelete) {
    const op = oldP as string;
    if (tree.get(op) === null) return fail('missing', op);
    tree.set(op, null);
    return null;
  }
  const op = oldP as string;
  const np = newP as string;
  const isMove = op !== np;
  if (isMove) {
    if (tree.get(op) === null) return fail('missing', op);
    if (tree.get(np) !== null) return fail('exists', np);
  } else {
    if (tree.get(op) === null) return fail('missing', op);
  }
  const cur = tree.get(op) as string;
  const model = parseFile(cur);
  const r = applyHunks(model, sec.hunks, strict, op);
  if ('code' in r) return r;
  if (isMove) {
    tree.set(np, serFile(r.model));
    tree.set(op, null);
    tree.moves.push({ old: op, nw: np });
  } else {
    tree.set(op, serFile(r.model));
  }
  return null;
}

// ---- SEARCH/REPLACE blocks (SPEC section 7) ----

interface SRBlock {
  path: string;
  oldLines: string[];
  newLines: string[];
}

function parseSR(lines: string[]): SRBlock[] {
  const blocks: SRBlock[] = [];
  let prevEnd = 0;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i].trimEnd() !== '<<<<<<< SEARCH') {
      i++;
      continue;
    }
    const searchIdx = i;
    let path: string | null = null;
    for (let j = searchIdx - 1; j >= prevEnd; j--) {
      const t = lines[j];
      if (t.trim() === '') continue;
      if (t.trim().startsWith('```')) continue;
      path = t.trim();
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new ParseErr(searchIdx + 1);
      path = prevPath;
    }
    let eq = -1;
    for (let j = searchIdx + 1; j < lines.length; j++) {
      if (lines[j].trimEnd() === '=======') {
        eq = j;
        break;
      }
    }
    let rep = -1;
    if (eq >= 0) {
      for (let j = eq + 1; j < lines.length; j++) {
        if (lines[j].trimEnd() === '>>>>>>> REPLACE') {
          rep = j;
          break;
        }
      }
    }
    if (eq < 0 || rep < 0) throw new ParseErr(searchIdx + 1);
    blocks.push({ path, oldLines: lines.slice(searchIdx + 1, eq), newLines: lines.slice(eq + 1, rep) });
    prevPath = path;
    prevEnd = rep + 1;
    i = rep + 1;
  }
  return blocks;
}

function applySR(tree: Tree, b: SRBlock, strict: boolean): Fail | null {
  if (!isSafe(b.path)) return fail('unsafe', b.path);
  if (b.oldLines.length === 0) {
    if (tree.get(b.path) !== null) return fail('exists', b.path);
    tree.set(b.path, serFile({ lines: [...b.newLines], brk: '\n', fin: b.newLines.length > 0 }));
    return null;
  }
  const cur = tree.get(b.path);
  if (cur === null) return fail('missing', b.path);
  const m = parseFile(cur);
  const f = findTier(m.lines, b.oldLines, strict);
  if (!f) return fail('no-match', b.path);
  if (f.pos.length !== 1) return fail('ambiguous', b.path);
  const at = f.pos[0];
  const repl = buildNewPlain(b.oldLines, b.newLines, m.lines, at, f.tier);
  const nl = [...m.lines];
  nl.splice(at, b.oldLines.length, ...repl);
  tree.set(b.path, serFile({ lines: nl, brk: m.brk, fin: m.fin }));
  return null;
}

// ---- V4A patches (SPEC section 8) ----

type V4ASection =
  | { kind: 'add'; path: string; fileLines: string[] }
  | { kind: 'del'; path: string }
  | { kind: 'upd'; path: string; moveTo: string | null; chunks: V4AChunk[] };

interface V4AChunk {
  anchor: string | null;
  eof: boolean;
  body: string[];
}

function parseV4A(lines: string[]): V4ASection[] {
  let first = -1;
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].trim() !== '') {
      first = i;
      break;
    }
  }
  if (first < 0 || lines[first].trim() !== '*** Begin Patch') {
    throw new ParseErr(first < 0 ? 1 : first + 1);
  }
  let last = -1;
  for (let i = lines.length - 1; i >= 0; i--) {
    if (lines[i].trim() !== '') {
      last = i;
      break;
    }
  }
  if (lines[last].trim() !== '*** End Patch') throw new ParseErr(lines.length + 1);
  const sections: V4ASection[] = [];
  let i = first + 1;
  const isSectionStart = (l: string): boolean =>
    l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ');
  while (i < last) {
    const line = lines[i];
    if (line.trim() === '') {
      i++;
      continue;
    }
    let kind: 'add' | 'del' | 'upd';
    let p: string;
    if (line.startsWith('*** Add File: ')) {
      kind = 'add';
      p = line.slice('*** Add File: '.length).trim();
    } else if (line.startsWith('*** Delete File: ')) {
      kind = 'del';
      p = line.slice('*** Delete File: '.length).trim();
    } else if (line.startsWith('*** Update File: ')) {
      kind = 'upd';
      p = line.slice('*** Update File: '.length).trim();
    } else {
      throw new ParseErr(i + 1);
    }
    const start = i + 1;
    let j = start;
    while (j < last && !isSectionStart(lines[j])) j++;
    const secLines = lines.slice(start, j);
    while (secLines.length > 0 && secLines[secLines.length - 1].trim() === '') secLines.pop();
    sections.push(parseV4ASection(kind, p, secLines, start, i + 1));
    i = j;
  }
  return sections;
}

function parseV4ASection(
  kind: 'add' | 'del' | 'upd',
  path: string,
  secLines: string[],
  start: number,
  headerLine: number,
): V4ASection {
  if (kind === 'add') {
    const fileLines: string[] = [];
    for (let k = 0; k < secLines.length; k++) {
      const l = secLines[k];
      if (l === '') fileLines.push('');
      else if (l[0] === '+') fileLines.push(l.slice(1));
      else throw new ParseErr(start + k + 1);
    }
    return { kind: 'add', path, fileLines };
  }
  if (kind === 'del') {
    if (secLines.length > 0) throw new ParseErr(start + 1);
    return { kind: 'del', path };
  }
  let moveTo: string | null = null;
  let rest = secLines;
  let restStart = start;
  if (rest.length > 0 && rest[0].startsWith('*** Move to: ')) {
    moveTo = rest[0].slice('*** Move to: '.length).trim();
    rest = rest.slice(1);
    restStart = start + 1;
  }
  const chunks: V4AChunk[] = [];
  let cur: V4AChunk | null = null;
  for (let k = 0; k < rest.length; k++) {
    const l = rest[k];
    const lineNo = restStart + k + 1;
    if (l.startsWith('@@')) {
      const t = l.slice(2).trim();
      cur = { anchor: t === '' ? null : t, eof: false, body: [] };
      chunks.push(cur);
      continue;
    }
    if (l === '*** End of File') {
      if (!cur) throw new ParseErr(lineNo);
      cur.eof = true;
      cur = null;
      continue;
    }
    if (l === '' || l[0] === ' ' || l[0] === '-' || l[0] === '+') {
      if (!cur) {
        if (chunks.length === 0) {
          cur = { anchor: null, eof: false, body: [] };
          chunks.push(cur);
        } else {
          throw new ParseErr(lineNo);
        }
      }
      cur.body.push(l);
      continue;
    }
    throw new ParseErr(lineNo);
  }
  if (chunks.length === 0 && moveTo === null) throw new ParseErr(headerLine);
  return { kind: 'upd', path, moveTo, chunks };
}

function applyV4A(tree: Tree, sec: V4ASection, strict: boolean): Fail | null {
  if (sec.kind === 'add') {
    if (!isSafe(sec.path)) return fail('unsafe', sec.path);
    if (tree.get(sec.path) !== null) return fail('exists', sec.path);
    tree.set(sec.path, serFile({ lines: [...sec.fileLines], brk: '\n', fin: sec.fileLines.length > 0 }));
    return null;
  }
  if (sec.kind === 'del') {
    if (!isSafe(sec.path)) return fail('unsafe', sec.path);
    if (tree.get(sec.path) === null) return fail('missing', sec.path);
    tree.set(sec.path, null);
    return null;
  }
  if (!isSafe(sec.path)) return fail('unsafe', sec.path);
  if (sec.moveTo !== null && !isSafe(sec.moveTo)) return fail('unsafe', sec.moveTo);
  const cur = tree.get(sec.path);
  if (cur === null) return fail('missing', sec.path);
  if (sec.moveTo !== null && tree.get(sec.moveTo) !== null) return fail('exists', sec.moveTo);
  const model = parseFile(cur);
  let lines = [...model.lines];
  let cursor = 0;
  for (const ch of sec.chunks) {
    if (ch.anchor !== null) {
      const ai = findAnchor(lines, ch.anchor, cursor, strict);
      if (ai < 0) return fail('no-match', sec.path);
      cursor = ai + 1;
    }
    const { o, nItems } = splitHunkBody(ch.body);
    if (o.length === 0) {
      const pos = ch.eof ? lines.length : cursor;
      const newLines = nItems.map((x) => x.text);
      lines.splice(pos, 0, ...newLines);
      cursor = pos + newLines.length;
      continue;
    }
    const f = findTierFrom(lines, o, cursor, strict);
    if (!f) return fail('no-match', sec.path);
    let at = -1;
    for (const p of f.pos) {
      if (ch.eof && p + o.length !== lines.length) continue;
      at = p;
      break;
    }
    if (at < 0) return fail('no-match', sec.path);
    const repl = buildNew(o, nItems, lines, at, f.tier);
    lines.splice(at, o.length, ...repl);
    cursor = at + repl.length;
  }
  const out = serFile({ lines, brk: model.brk, fin: model.fin });
  if (sec.moveTo !== null) {
    tree.set(sec.moveTo, out);
    tree.set(sec.path, null);
    tree.moves.push({ old: sec.path, nw: sec.moveTo });
  } else {
    tree.set(sec.path, out);
  }
  return null;
}

// ---- JSON edits (SPEC section 9) ----

type JsonEdit =
  | { cmd: 'create'; path: string; file_text: string }
  | { cmd: 'str_replace'; path: string; old_str: string; new_str: string }
  | { cmd: 'insert'; path: string; insert_line: number; new_str: string };

function validateJsonEdit(o: unknown, lineNo: number): JsonEdit {
  if (typeof o !== 'object' || o === null || Array.isArray(o)) throw new ParseErr(lineNo);
  const rec = o as Record<string, unknown>;
  const path = rec.path;
  const cmd = rec.command;
  if (typeof path !== 'string' || typeof cmd !== 'string') throw new ParseErr(lineNo);
  if (cmd === 'create') {
    if (typeof rec.file_text !== 'string') throw new ParseErr(lineNo);
    return { cmd, path, file_text: rec.file_text };
  }
  if (cmd === 'str_replace') {
    if (typeof rec.old_str !== 'string' || rec.old_str === '') throw new ParseErr(lineNo);
    let ns = rec.new_str;
    if (ns === undefined) ns = '';
    if (typeof ns !== 'string') throw new ParseErr(lineNo);
    return { cmd, path, old_str: rec.old_str, new_str: ns };
  }
  if (cmd === 'insert') {
    if (typeof rec.insert_line !== 'number' || !Number.isInteger(rec.insert_line)) throw new ParseErr(lineNo);
    if (typeof rec.new_str !== 'string') throw new ParseErr(lineNo);
    return { cmd, path, insert_line: rec.insert_line, new_str: rec.new_str };
  }
  throw new ParseErr(lineNo);
}

function parseJSON(lines: string[], patchText: string): JsonEdit[] {
  let first = -1;
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].trim() !== '') {
      first = i;
      break;
    }
  }
  if (first < 0) return [];
  const firstCh = lines[first].trimStart()[0];
  if (firstCh === '[') {
    let arr: unknown;
    try {
      arr = JSON.parse(patchText);
    } catch {
      throw new ParseErr(first + 1);
    }
    if (!Array.isArray(arr)) throw new ParseErr(first + 1);
    return arr.map((o) => validateJsonEdit(o, first + 1));
  }
  const edits: JsonEdit[] = [];
  for (let i = 0; i < lines.length; i++) {
    const l = lines[i];
    if (l.trim() === '') continue;
    let o: unknown;
    try {
      o = JSON.parse(l);
    } catch {
      throw new ParseErr(i + 1);
    }
    edits.push(validateJsonEdit(o, i + 1));
  }
  return edits;
}

function applyJSON(tree: Tree, ed: JsonEdit): Fail | null {
  if (!isSafe(ed.path)) return fail('unsafe', ed.path);
  if (ed.cmd === 'create') {
    if (tree.get(ed.path) !== null) return fail('exists', ed.path);
    tree.set(ed.path, ed.file_text);
    return null;
  }
  const cur = tree.get(ed.path);
  if (cur === null) return fail('missing', ed.path);
  if (ed.cmd === 'str_replace') {
    const m = parseFile(cur);
    if (m.brk === '\r\n') {
      const text = cur.replace(/\r\n/g, '\n');
      const oldS = ed.old_str.replace(/\r\n/g, '\n');
      const newS = ed.new_str.replace(/\r\n/g, '\n');
      const c = countOcc(text, oldS);
      if (c === 0) return fail('no-match', ed.path);
      if (c > 1) return fail('ambiguous', ed.path);
      tree.set(ed.path, text.replace(oldS, newS).replace(/\n/g, '\r\n'));
    } else {
      const c = countOcc(cur, ed.old_str);
      if (c === 0) return fail('no-match', ed.path);
      if (c > 1) return fail('ambiguous', ed.path);
      tree.set(ed.path, cur.replace(ed.old_str, ed.new_str));
    }
    return null;
  }
  const m = parseFile(cur);
  if (ed.insert_line < 0 || ed.insert_line > m.lines.length) return fail('no-match', ed.path);
  // An empty new_str has no lines (SPEC section 9).
  const ins = ed.new_str === '' ? [] : patchLines(ed.new_str);
  const nl = [...m.lines];
  nl.splice(ed.insert_line, 0, ...ins);
  tree.set(ed.path, serFile({ lines: nl, brk: m.brk, fin: m.fin }));
  return null;
}

// ---- Driver (SPEC sections 1, 2, 10) ----

type Edit =
  | { fmt: 'unified'; sec: UniSection }
  | { fmt: 'search-replace'; block: SRBlock }
  | { fmt: 'v4a'; sec: V4ASection }
  | { fmt: 'json'; ed: JsonEdit };

function applyEdit(tree: Tree, ed: Edit, strict: boolean): Fail | null {
  if (ed.fmt === 'unified') return applyUnified(tree, ed.sec, strict);
  if (ed.fmt === 'search-replace') return applySR(tree, ed.block, strict);
  if (ed.fmt === 'v4a') return applyV4A(tree, ed.sec, strict);
  return applyJSON(tree, ed.ed);
}

function byteCompare(a: string, b: string): number {
  return Buffer.compare(Buffer.from(a, 'utf8'), Buffer.from(b, 'utf8'));
}

function writeTree(tree: Tree): void {
  for (const p of tree.touched) {
    const after = tree.cur.get(p) ?? null;
    const full = join(process.cwd(), ...p.split('/'));
    if (after === null) {
      try {
        unlinkSync(full);
      } catch {
        // Already absent.
      }
    } else {
      mkdirSync(dirname(full), { recursive: true });
      writeFileSync(full, after);
    }
  }
}

function run(args: string[]): { code: number; out: string[] } {
  let format = 'auto';
  let check = false;
  let strict = false;
  const positional: string[] = [];
  const seen = new Set<string>();
  let endOpts = false;
  for (const a of args) {
    if (!endOpts && a === '--') {
      endOpts = true;
      continue;
    }
    if (!endOpts && a.startsWith('-') && a !== '-') {
      if (a === '--check') {
        if (seen.has('check')) return usage();
        seen.add('check');
        check = true;
      } else if (a === '--strict') {
        if (seen.has('strict')) return usage();
        seen.add('strict');
        strict = true;
      } else if (a.startsWith('--format=')) {
        if (seen.has('format')) return usage();
        seen.add('format');
        const v = a.slice('--format='.length);
        if (v !== 'auto' && v !== 'unified' && v !== 'search-replace' && v !== 'v4a' && v !== 'json') return usage();
        format = v;
      } else {
        return usage();
      }
    } else {
      positional.push(a);
    }
  }
  if (positional.length > 1) return usage();
  let patchText: string;
  const patchArg = positional[0];
  if (patchArg === undefined || patchArg === '-') {
    try {
      patchText = readFileSync(0, 'utf8');
    } catch {
      return { code: 2, out: ['error: no-patch'] };
    }
  } else {
    try {
      patchText = readFileSync(patchArg, 'utf8');
    } catch {
      return { code: 2, out: ['error: no-patch'] };
    }
  }
  const lines = patchLines(patchText);
  let fmt = format;
  if (fmt === 'auto') {
    const det = detectFormat(lines);
    if (!det) return { code: 2, out: ['error: format'] };
    fmt = det;
  }
  let edits: Edit[];
  try {
    if (fmt === 'unified') edits = parseUnified(lines).map((sec) => ({ fmt: 'unified' as const, sec }));
    else if (fmt === 'search-replace') edits = parseSR(lines).map((block) => ({ fmt: 'search-replace' as const, block }));
    else if (fmt === 'v4a') edits = parseV4A(lines).map((sec) => ({ fmt: 'v4a' as const, sec }));
    else edits = parseJSON(lines, patchText).map((ed) => ({ fmt: 'json' as const, ed }));
  } catch (e) {
    if (e instanceof ParseErr) return { code: 2, out: [`error: parse ${e.line}`] };
    throw e;
  }
  if (edits.length === 0) return { code: 2, out: ['error: parse 1'] };
  const tree = new Tree();
  const failures: Fail[] = [];
  for (const ed of edits) {
    const f = applyEdit(tree, ed, strict);
    if (f) failures.push(f);
  }
  if (failures.length > 0) {
    const out = failures.map((f) => `error: ${f.code} ${f.path}`);
    out.push(`failed: ${failures.length} of ${edits.length} edits`);
    return { code: 1, out };
  }
  if (!check) writeTree(tree);
  const changes = new Map<string, { before: string | null; after: string | null }>();
  for (const p of tree.touched) {
    const before = tree.init.get(p) ?? null;
    const after = tree.cur.get(p) ?? null;
    if (before === after) continue;
    changes.set(p, { before, after });
  }
  const outLines: Array<{ key: string; line: string }> = [];
  for (const mv of tree.moves) {
    const dc = changes.get(mv.old);
    const ac = changes.get(mv.nw);
    if (!dc || !ac) continue;
    if (dc.before === null || dc.after !== null) continue;
    if (ac.before !== null || ac.after === null) continue;
    outLines.push({ key: mv.nw, line: `R ${mv.old} -> ${mv.nw}` });
    changes.delete(mv.old);
    changes.delete(mv.nw);
  }
  for (const [p, c] of changes) {
    if (c.before === null) outLines.push({ key: p, line: `A ${p}` });
    else if (c.after === null) outLines.push({ key: p, line: `D ${p}` });
    else outLines.push({ key: p, line: `M ${p}` });
  }
  outLines.sort((x, y) => byteCompare(x.key, y.key));
  const out = outLines.map((e) => e.line);
  out.push(`ok: ${outLines.length} ${outLines.length === 1 ? 'file' : 'files'}`);
  return { code: 0, out };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
