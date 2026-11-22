// mend: one patch tool for every AI edit format.
//
// Applies a patch in one of four formats (unified diff, SEARCH/REPLACE
// blocks, V4A, JSON edits) to the tree rooted at the working directory.
// See SPEC.md for the whole contract. Node 22 standard library only.
//
// When MAKEFUN_ENV_URL is set, the trial is handed over to runner.ts
// (runTrial), which runs this program on each of the trial's checks.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync } from 'node:fs';
import { dirname } from 'node:path';
import { runTrial } from './runner.ts';

// ---------------------------------------------------------------- helpers

const isBlank = (s: string): boolean => /^\s*$/.test(s);
const trimTrailST = (s: string): string => s.replace(/[ \t]+$/, '');
const trimST = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
const leadWs = (s: string): string => {
  const m = /^[ \t]*/.exec(s);
  return m === null ? '' : m[0];
};

/** A parse fault: the patch cannot be read in its format at this line. */
class ParseErr extends Error {
  line: number;
  constructor(line: number) {
    super(`parse ${line}`);
    this.line = line;
  }
}

type Fail = { code: string; path: string };
type EditFn = (tree: Tree, strict: boolean) => Fail | null;

// ------------------------------------------------------- files and lines

interface FileState {
  lines: string[];
  brk: '\r\n' | '\n';
  eol: boolean;
}

/** Split a file's text into lines under its own line break. */
function splitFile(text: string): FileState {
  if (text === '') return { lines: [], brk: '\n', eol: false };
  const lf = text.indexOf('\n');
  const brk: '\r\n' | '\n' = lf > 0 && text.charAt(lf - 1) === '\r' ? '\r\n' : '\n';
  const parts = text.split(brk);
  let eol = false;
  if (parts.length > 0 && parts[parts.length - 1] === '') {
    parts.pop();
    eol = true;
  }
  return { lines: parts, brk, eol };
}

function joinFile(f: FileState): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.brk) + (f.eol ? f.brk : '');
}

/** A patch's lines: split at \n, one trailing \r removed, no empty piece
 *  after a final \n. */
function splitPatch(text: string): string[] {
  const lines = text.split('\n').map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
  if (text.endsWith('\n') && lines.length > 0) lines.pop();
  return lines;
}

// ------------------------------------------------------------- matching

function keyAt(s: string, tier: number): string {
  if (tier === 0) return s;
  if (tier === 1) return trimTrailST(s);
  return trimST(s);
}

function findOccurrences(lines: string[], pat: string[], tier: number): number[] {
  const out: number[] = [];
  const k = pat.length;
  if (k === 0 || k > lines.length) return out;
  for (let i = 0; i + k <= lines.length; i++) {
    let ok = true;
    for (let j = 0; j < k; j++) {
      if (keyAt(lines[i + j], tier) !== keyAt(pat[j], tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

function tiersToTry(strict: boolean): number[] {
  return strict ? [0] : [0, 1, 2];
}

/** First tier at which pat occurs in lines, or null. */
function firstTier(lines: string[], pat: string[], strict: boolean): number | null {
  for (const t of tiersToTry(strict)) {
    if (findOccurrences(lines, pat, t).length > 0) return t;
  }
  return null;
}

interface NewLine {
  text: string;
  /** Index into O when this is a context line, else null. */
  ctx: number | null;
}

/**
 * Build the replacement lines: a context line is written as the file's own
 * matched line; at tier 2 every other line is re-indented from O's first
 * line's leading whitespace to the file's first matched line's.
 */
function buildNew(lines: string[], pat: string[], news: NewLine[], pos: number, tier: number): string[] {
  let f = '';
  let p = '';
  if (pat.length > 0 && pos < lines.length) {
    f = leadWs(lines[pos]);
    p = leadWs(pat[0]);
  }
  const out: string[] = [];
  for (const e of news) {
    if (e.ctx !== null) {
      out.push(lines[pos + e.ctx]);
      continue;
    }
    if (tier === 2 && pat.length > 0) {
      const t = e.text;
      if (t !== '' && !/^[ \t]+$/.test(t) && t.startsWith(p)) {
        out.push(f + t.slice(p.length));
        continue;
      }
    }
    out.push(e.text);
  }
  return out;
}

// ------------------------------------------------------------------- tree

/** The working tree as the edits leave it, over the files on disk. */
class Tree {
  /** Disk bytes of every path read from disk. */
  initial = new Map<string, string>();
  /** Current state of every path touched: text, or null when absent. */
  state = new Map<string, string | null>();
  /** Successful moves, for the R output lines. */
  moves: { old: string; next: string }[] = [];

  private diskKind(p: string): 'file' | 'other' | 'absent' {
    try {
      const st = statSync(p);
      return st.isFile() ? 'file' : 'other';
    } catch {
      return 'absent';
    }
  }

  existsAny(p: string): boolean {
    if (this.state.has(p)) return this.state.get(p) !== null;
    return this.diskKind(p) !== 'absent';
  }

  existsFile(p: string): boolean {
    if (this.state.has(p)) return this.state.get(p) !== null;
    return this.diskKind(p) === 'file';
  }

  getText(p: string): string | null {
    if (this.state.has(p)) return this.state.get(p);
    if (this.diskKind(p) === 'file') {
      const text = readFileSync(p, 'utf8');
      this.initial.set(p, text);
      this.state.set(p, text);
      return text;
    }
    this.state.set(p, null);
    return null;
  }

  set(p: string, text: string | null): void {
    // First touch of a path for writing: remember what was on disk, so a
    // deletion or a move still knows the path existed before the patch.
    if (!this.state.has(p) && !this.initial.has(p) && this.diskKind(p) === 'file') {
      this.initial.set(p, readFileSync(p, 'utf8'));
    }
    this.state.set(p, text);
  }
}

function isSafe(p: string): boolean {
  if (p === '') return false;
  if (p.startsWith('/')) return false;
  if (p.includes('\\')) return false;
  for (const seg of p.split('/')) {
    if (seg === '' || seg === '.' || seg === '..') return false;
  }
  return true;
}

// --------------------------------------------------------- unified diffs

interface Hunk {
  a: number;
  body: string[];
}

interface UnifiedSection {
  pairOld: string | null;
  pairNew: string | null;
  renameOld: string | null;
  renameNew: string | null;
  diffOld: string | null;
  diffNew: string | null;
  newFile: boolean;
  deletedFile: boolean;
  hunks: Hunk[];
}

function diffPath(raw: string): string | null {
  const cut = raw.split('\t')[0].trim();
  if (cut === '/dev/null') return null;
  if (cut.startsWith('a/') || cut.startsWith('b/')) return cut.slice(2);
  return cut;
}

function parseUnified(lines: string[]): EditFn[] {
  const sections: UnifiedSection[] = [];
  let cur: UnifiedSection | null = null;
  let inHeader = false;
  let i = 0;
  const n = lines.length;
  const newSection = (diffOld: string | null, diffNew: string | null): UnifiedSection => {
    const s: UnifiedSection = {
      pairOld: null,
      pairNew: null,
      renameOld: null,
      renameNew: null,
      diffOld,
      diffNew,
      newFile: false,
      deletedFile: false,
      hunks: [],
    };
    sections.push(s);
    return s;
  };
  while (i < n) {
    const line = lines[i];
    if (line.startsWith('diff --git ')) {
      const m = /^diff --git a\/(\S+) b\/(\S+)$/.exec(line.replace(/[ \t]+$/, ''));
      if (m === null) throw new ParseErr(i + 1);
      cur = newSection(m[1], m[2]);
      inHeader = true;
      i += 1;
      continue;
    }
    if (line.startsWith('--- ') && i + 1 < n && lines[i + 1].startsWith('+++ ')) {
      if (cur !== null && inHeader) {
        cur.pairOld = diffPath(line.slice(4));
        cur.pairNew = diffPath(lines[i + 1].slice(4));
      } else {
        cur = newSection(null, null);
        cur.pairOld = diffPath(line.slice(4));
        cur.pairNew = diffPath(lines[i + 1].slice(4));
        inHeader = true;
      }
      i += 2;
      continue;
    }
    if (line.startsWith('@@')) {
      if (cur === null) throw new ParseErr(i + 1);
      const m = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/.exec(line);
      if (m === null) throw new ParseErr(i + 1);
      inHeader = false;
      const a = Number(m[1]);
      i += 1;
      const body: string[] = [];
      while (i < n) {
        const bl = lines[i];
        if (bl.startsWith('diff --git ')) break;
        if (bl.startsWith('--- ') && i + 1 < n && lines[i + 1].startsWith('+++ ')) break;
        if (bl === '' || bl.startsWith(' ') || bl.startsWith('-') || bl.startsWith('+') || bl.startsWith('\\')) {
          body.push(bl);
          i += 1;
          continue;
        }
        break;
      }
      while (body.length > 0 && (body[body.length - 1] === '' || body[body.length - 1] === ' ')) body.pop();
      cur.hunks.push({ a, body });
      continue;
    }
    if (cur === null) {
      i += 1;
      continue;
    }
    if (inHeader) {
      if (line.startsWith('--- ')) throw new ParseErr(i + 2);
      if (line.startsWith('+++ ')) {
        cur.pairNew = diffPath(line.slice(4));
        i += 1;
        continue;
      }
      if (line.startsWith('rename from ')) {
        cur.renameOld = line.slice(12).trim();
        i += 1;
        continue;
      }
      if (line.startsWith('rename to ')) {
        cur.renameNew = line.slice(10).trim();
        i += 1;
        continue;
      }
      if (line.startsWith('new file mode')) {
        cur.newFile = true;
        i += 1;
        continue;
      }
      if (line.startsWith('deleted file mode')) {
        cur.deletedFile = true;
        i += 1;
        continue;
      }
      i += 1;
      continue;
    }
    i += 1;
  }
  if (sections.length === 0) throw new ParseErr(1);
  return sections.map((s) => (tree: Tree, strict: boolean) => applyUnifiedSection(s, tree, strict));
}

/** Whether a `\` line follows the hunk's last context or `+` line. */
function hunkNoNewline(body: string[]): boolean {
  let last = -1;
  for (let j = 0; j < body.length; j++) {
    if (body[j].startsWith(' ') || body[j].startsWith('+')) last = j;
  }
  return last >= 0 && body[last + 1] !== undefined && body[last + 1].startsWith('\\');
}

/** Split a hunk body into old lines O and new lines N (with context marks). */
function hunkLines(body: string[]): { o: string[]; n: NewLine[] } {
  const o: string[] = [];
  const n: NewLine[] = [];
  for (const bl of body) {
    if (bl.startsWith('\\')) continue;
    if (bl.startsWith(' ')) {
      const t = bl.slice(1);
      o.push(t);
      n.push({ text: t, ctx: o.length - 1 });
    } else if (bl.startsWith('-')) {
      o.push(bl.slice(1));
    } else if (bl.startsWith('+')) {
      n.push({ text: bl.slice(1), ctx: null });
    } else if (bl === '') {
      o.push('');
      n.push({ text: '', ctx: o.length - 1 });
    }
  }
  return { o, n };
}

function applyHunks(text: string, hunks: Hunk[], strict: boolean, path: string): { text: string } | { fail: Fail } {
  const f = splitFile(text);
  let d = 0;
  for (const h of hunks) {
    const { o, n } = hunkLines(h.body);
    const noNl = hunkNoNewline(h.body);
    if (o.length === 0) {
      const ins = Math.min(h.a + d, f.lines.length);
      const atEnd = ins === f.lines.length;
      const news = n.map((e) => e.text);
      f.lines.splice(ins, 0, ...news);
      if (atEnd) f.eol = !noNl;
      d += n.length;
      continue;
    }
    const tier = firstTier(f.lines, o, strict);
    if (tier === null) return { fail: { code: 'no-match', path } };
    const occ = findOccurrences(f.lines, o, tier);
    const target = h.a - 1 + d;
    let best = occ[0];
    let bestDist = Math.abs(occ[0] - target);
    for (let k = 1; k < occ.length; k++) {
      const dist = Math.abs(occ[k] - target);
      if (dist < bestDist) {
        best = occ[k];
        bestDist = dist;
      }
    }
    const atEnd = best + o.length === f.lines.length;
    const news = buildNew(f.lines, o, n, best, tier);
    f.lines.splice(best, o.length, ...news);
    if (atEnd) f.eol = !noNl;
    d += n.length - o.length;
  }
  return { text: joinFile(f) };
}

function applyUnifiedSection(s: UnifiedSection, tree: Tree, strict: boolean): Fail | null {
  const oldPath = s.pairOld ?? s.renameOld ?? s.diffOld;
  const newPath = s.pairNew ?? s.renameNew ?? s.diffNew;
  const isCreate = s.newFile || oldPath === null;
  if (isCreate) {
    const target = newPath;
    if (target === null) return { code: 'unsafe', path: '' };
    if (!isSafe(target)) return { code: 'unsafe', path: target };
    if (tree.existsAny(target)) return { code: 'exists', path: target };
    const plus: string[] = [];
    let noNl = false;
    for (let h = s.hunks.length - 1; h >= 0; h--) {
      const body = s.hunks[h].body;
      let lastPlus = -1;
      for (let j = 0; j < body.length; j++) if (body[j].startsWith('+')) lastPlus = j;
      if (lastPlus >= 0) {
        noNl = body[lastPlus + 1] !== undefined && body[lastPlus + 1].startsWith('\\');
        break;
      }
    }
    for (const h of s.hunks) {
      for (const bl of h.body) if (bl.startsWith('+')) plus.push(bl.slice(1));
    }
    tree.set(target, plus.length === 0 ? '' : plus.join('\n') + (noNl ? '' : '\n'));
    return null;
  }
  const isDelete = s.deletedFile || newPath === null;
  if (isDelete) {
    const target = oldPath;
    if (target === null) return { code: 'unsafe', path: '' };
    if (!isSafe(target)) return { code: 'unsafe', path: target };
    if (!tree.existsFile(target)) return { code: 'missing', path: target };
    tree.set(target, null);
    return null;
  }
  if (oldPath !== newPath) {
    if (oldPath === null || newPath === null) return { code: 'unsafe', path: '' };
    if (!isSafe(oldPath)) return { code: 'unsafe', path: oldPath };
    if (!isSafe(newPath)) return { code: 'unsafe', path: newPath };
    if (!tree.existsFile(oldPath)) return { code: 'missing', path: oldPath };
    if (tree.existsAny(newPath)) return { code: 'exists', path: newPath };
    const cur = tree.getText(oldPath);
    if (cur === null) return { code: 'missing', path: oldPath };
    const r = applyHunks(cur, s.hunks, strict, oldPath);
    if ('fail' in r) return r.fail;
    tree.set(newPath, r.text);
    tree.set(oldPath, null);
    tree.moves.push({ old: oldPath, next: newPath });
    return null;
  }
  const target = oldPath as string;
  if (!isSafe(target)) return { code: 'unsafe', path: target };
  if (!tree.existsFile(target)) return { code: 'missing', path: target };
  const cur = tree.getText(target);
  if (cur === null) return { code: 'missing', path: target };
  const r = applyHunks(cur, s.hunks, strict, target);
  if ('fail' in r) return r.fail;
  tree.set(target, r.text);
  return null;
}

// --------------------------------------------------- SEARCH/REPLACE blocks

interface SREdit {
  path: string;
  oldLines: string[];
  newLines: string[];
}

function parseSearchReplace(lines: string[]): EditFn[] {
  const edits: SREdit[] = [];
  let prevEnd = -1;
  let prevPath: string | null = null;
  let i = 0;
  const n = lines.length;
  while (i < n) {
    if (trimTrailST(lines[i]) === '<<<<<<< SEARCH') {
      const searchLine = i + 1;
      let path: string | null = null;
      for (let j = i - 1; j > prevEnd; j--) {
        const t = lines[j];
        if (isBlank(t)) continue;
        const tr = t.trim();
        if (tr.startsWith('```')) continue;
        path = tr;
        break;
      }
      if (path === null) {
        if (prevPath === null) throw new ParseErr(searchLine);
        path = prevPath;
      }
      let j = i + 1;
      let eq = -1;
      while (j < n) {
        if (trimTrailST(lines[j]) === '=======') {
          eq = j;
          break;
        }
        j += 1;
      }
      if (eq === -1) throw new ParseErr(searchLine);
      let k = eq + 1;
      let rep = -1;
      while (k < n) {
        if (trimTrailST(lines[k]) === '>>>>>>> REPLACE') {
          rep = k;
          break;
        }
        k += 1;
      }
      if (rep === -1) throw new ParseErr(searchLine);
      edits.push({ path, oldLines: lines.slice(i + 1, eq), newLines: lines.slice(eq + 1, rep) });
      prevPath = path;
      prevEnd = rep;
      i = rep + 1;
      continue;
    }
    i += 1;
  }
  if (edits.length === 0) throw new ParseErr(1);
  return edits.map((e) => (tree: Tree, strict: boolean) => applySREdit(e, tree, strict));
}

function applySREdit(e: SREdit, tree: Tree, strict: boolean): Fail | null {
  if (!isSafe(e.path)) return { code: 'unsafe', path: e.path };
  if (e.oldLines.length === 0) {
    if (tree.existsAny(e.path)) return { code: 'exists', path: e.path };
    tree.set(e.path, e.newLines.length === 0 ? '' : e.newLines.join('\n') + '\n');
    return null;
  }
  if (!tree.existsFile(e.path)) return { code: 'missing', path: e.path };
  const cur = tree.getText(e.path);
  if (cur === null) return { code: 'missing', path: e.path };
  const f = splitFile(cur);
  const tier = firstTier(f.lines, e.oldLines, strict);
  if (tier === null) return { code: 'no-match', path: e.path };
  const occ = findOccurrences(f.lines, e.oldLines, tier);
  if (occ.length > 1) return { code: 'ambiguous', path: e.path };
  const pos = occ[0];
  const news = buildNew(
    f.lines,
    e.oldLines,
    e.newLines.map((t) => ({ text: t, ctx: null })),
    pos,
    tier,
  );
  f.lines.splice(pos, e.oldLines.length, ...news);
  tree.set(e.path, joinFile(f));
  return null;
}

// ------------------------------------------------------------ V4A patches

interface V4AChunk {
  anchor: string | null;
  eof: boolean;
  body: string[];
}

interface V4AAdd {
  kind: 'add';
  path: string;
  content: string[];
}
interface V4ADelete {
  kind: 'delete';
  path: string;
}
interface V4AUpdate {
  kind: 'update';
  path: string;
  moveTo: string | null;
  chunks: V4AChunk[];
}
type V4AEdit = V4AAdd | V4ADelete | V4AUpdate;

interface RawLine {
  text: string;
  no: number;
}

function parseV4AUpdate(path: string, raw: RawLine[], updateLine: number): V4AUpdate {
  let moveTo: string | null = null;
  let k = 0;
  if (k < raw.length && raw[k].text.startsWith('*** Move to:')) {
    moveTo = raw[k].text.slice(12).trim();
    k += 1;
  }
  const chunks: V4AChunk[] = [];
  let cur: V4AChunk | null = null;
  let sawChunk = false;
  let afterEof = false;
  while (k < raw.length) {
    const r = raw[k];
    const t = r.text;
    if (t.startsWith('*** Move to:')) throw new ParseErr(r.no);
    if (t === '*** End of File') {
      if (cur === null) throw new ParseErr(r.no);
      cur.eof = true;
      cur = null;
      afterEof = true;
      k += 1;
      continue;
    }
    if (t.startsWith('@@')) {
      cur = { anchor: t.slice(2).trim(), eof: false, body: [] };
      chunks.push(cur);
      sawChunk = true;
      afterEof = false;
      k += 1;
      continue;
    }
    if (t.startsWith('***')) throw new ParseErr(r.no);
    if (t === '' || t.startsWith(' ') || t.startsWith('-') || t.startsWith('+')) {
      if (cur === null) {
        if (sawChunk || afterEof) throw new ParseErr(r.no);
        cur = { anchor: null, eof: false, body: [] };
        chunks.push(cur);
        sawChunk = true;
      }
      cur.body.push(t);
      k += 1;
      continue;
    }
    throw new ParseErr(r.no);
  }
  if (chunks.length === 0 && moveTo === null) throw new ParseErr(updateLine);
  return { kind: 'update', path, moveTo, chunks };
}

function parseV4A(lines: string[]): EditFn[] {
  let first = -1;
  for (let i = 0; i < lines.length; i++) {
    if (!isBlank(lines[i])) {
      first = i;
      break;
    }
  }
  if (first === -1) throw new ParseErr(1);
  if (lines[first].trim() !== '*** Begin Patch') throw new ParseErr(first + 1);
  let last = -1;
  for (let i = lines.length - 1; i >= 0; i--) {
    if (!isBlank(lines[i])) {
      last = i;
      break;
    }
  }
  if (last === -1 || lines[last].trim() !== '*** End Patch') throw new ParseErr(lines.length + 1);
  const edits: V4AEdit[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i];
    if (isBlank(line)) {
      i += 1;
      continue;
    }
    let kind: 'add' | 'delete' | 'update';
    let path: string;
    if (line.startsWith('*** Add File:')) {
      kind = 'add';
      path = line.slice(13).trim();
    } else if (line.startsWith('*** Delete File:')) {
      kind = 'delete';
      path = line.slice(16).trim();
    } else if (line.startsWith('*** Update File:')) {
      kind = 'update';
      path = line.slice(16).trim();
    } else {
      throw new ParseErr(i + 1);
    }
    const raw: RawLine[] = [];
    let j = i + 1;
    while (j < last) {
      const l = lines[j];
      if (l.startsWith('*** Add File:') || l.startsWith('*** Delete File:') || l.startsWith('*** Update File:')) break;
      raw.push({ text: l, no: j + 1 });
      j += 1;
    }
    while (raw.length > 0 && isBlank(raw[raw.length - 1].text)) raw.pop();
    if (kind === 'add') {
      const content: string[] = [];
      for (const r of raw) {
        if (r.text === '') content.push('');
        else if (r.text.startsWith('+')) content.push(r.text.slice(1));
        else throw new ParseErr(r.no);
      }
      edits.push({ kind: 'add', path, content });
    } else if (kind === 'delete') {
      for (const r of raw) {
        if (!isBlank(r.text)) throw new ParseErr(r.no);
      }
      edits.push({ kind: 'delete', path });
    } else {
      edits.push(parseV4AUpdate(path, raw, i + 1));
    }
    i = j;
  }
  if (edits.length === 0) throw new ParseErr(1);
  return edits.map((e) => (tree: Tree, strict: boolean) => applyV4AEdit(e, tree, strict));
}

/** First tier at which the single anchor line occurs at or after `from`. */
function firstTierSingle(lines: string[], anchor: string, from: number, strict: boolean): number | null {
  for (const t of tiersToTry(strict)) {
    for (let i = from; i < lines.length; i++) {
      if (keyAt(lines[i], t) === keyAt(anchor, t)) return t;
    }
  }
  return null;
}

function findFirstSingle(lines: string[], anchor: string, from: number, tier: number): number {
  for (let i = from; i < lines.length; i++) {
    if (keyAt(lines[i], tier) === keyAt(anchor, tier)) return i;
  }
  return -1;
}

function findOccurrencesFrom(lines: string[], pat: string[], tier: number, from: number, eof: boolean): number[] {
  const out: number[] = [];
  const k = pat.length;
  if (k === 0) return out;
  for (let i = from; i + k <= lines.length; i++) {
    if (eof && i + k !== lines.length) continue;
    let ok = true;
    for (let j = 0; j < k; j++) {
      if (keyAt(lines[i + j], tier) !== keyAt(pat[j], tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

function applyV4AEdit(e: V4AEdit, tree: Tree, strict: boolean): Fail | null {
  if (e.kind === 'add') {
    if (!isSafe(e.path)) return { code: 'unsafe', path: e.path };
    if (tree.existsAny(e.path)) return { code: 'exists', path: e.path };
    tree.set(e.path, e.content.length === 0 ? '' : e.content.join('\n') + '\n');
    return null;
  }
  if (e.kind === 'delete') {
    if (!isSafe(e.path)) return { code: 'unsafe', path: e.path };
    if (!tree.existsFile(e.path)) return { code: 'missing', path: e.path };
    tree.set(e.path, null);
    return null;
  }
  if (!isSafe(e.path)) return { code: 'unsafe', path: e.path };
  if (e.moveTo !== null && !isSafe(e.moveTo)) return { code: 'unsafe', path: e.moveTo };
  if (!tree.existsFile(e.path)) return { code: 'missing', path: e.path };
  if (e.moveTo !== null && tree.existsAny(e.moveTo)) return { code: 'exists', path: e.moveTo };
  const cur = tree.getText(e.path);
  if (cur === null) return { code: 'missing', path: e.path };
  const f = splitFile(cur);
  let cursor = 0;
  for (const ch of e.chunks) {
    if (ch.anchor !== null && ch.anchor !== '') {
      const tier = firstTierSingle(f.lines, ch.anchor, cursor, strict);
      if (tier === null) return { code: 'no-match', path: e.path };
      const idx = findFirstSingle(f.lines, ch.anchor, cursor, tier);
      if (idx === -1) return { code: 'no-match', path: e.path };
      cursor = idx + 1;
    }
    const o: string[] = [];
    const n: NewLine[] = [];
    for (const bl of ch.body) {
      if (bl.startsWith(' ')) {
        const t = bl.slice(1);
        o.push(t);
        n.push({ text: t, ctx: o.length - 1 });
      } else if (bl.startsWith('-')) {
        o.push(bl.slice(1));
      } else if (bl.startsWith('+')) {
        n.push({ text: bl.slice(1), ctx: null });
      } else if (bl === '') {
        o.push('');
        n.push({ text: '', ctx: o.length - 1 });
      }
    }
    if (o.length === 0) {
      const ins = ch.eof ? f.lines.length : cursor;
      const news = n.map((x) => x.text);
      f.lines.splice(ins, 0, ...news);
      cursor = ins + news.length;
      continue;
    }
    let tier: number | null = null;
    let occ: number[] = [];
    for (const t of tiersToTry(strict)) {
      occ = findOccurrencesFrom(f.lines, o, t, cursor, ch.eof);
      if (occ.length > 0) {
        tier = t;
        break;
      }
    }
    if (tier === null || occ.length === 0) return { code: 'no-match', path: e.path };
    const pos = occ[0];
    const news = buildNew(f.lines, o, n, pos, tier);
    f.lines.splice(pos, o.length, ...news);
    cursor = pos + news.length;
  }
  const text = joinFile(f);
  if (e.moveTo !== null) {
    tree.set(e.moveTo, text);
    tree.set(e.path, null);
    tree.moves.push({ old: e.path, next: e.moveTo });
  } else {
    tree.set(e.path, text);
  }
  return null;
}

// ------------------------------------------------------------- JSON edits

interface JsonEdit {
  command: string;
  path: string;
  fileText?: string;
  oldStr?: string;
  newStr?: string;
  insertLine?: number;
}

function validateJsonEdit(obj: unknown, line: number): JsonEdit {
  if (obj === null || typeof obj !== 'object' || Array.isArray(obj)) throw new ParseErr(line);
  const o = obj as Record<string, unknown>;
  if (typeof o.path !== 'string') throw new ParseErr(line);
  if (typeof o.command !== 'string') throw new ParseErr(line);
  if (o.command === 'create') {
    if (typeof o.file_text !== 'string') throw new ParseErr(line);
    return { command: 'create', path: o.path, fileText: o.file_text };
  }
  if (o.command === 'str_replace') {
    if (typeof o.old_str !== 'string' || o.old_str === '') throw new ParseErr(line);
    if (o.new_str !== undefined && typeof o.new_str !== 'string') throw new ParseErr(line);
    return {
      command: 'str_replace',
      path: o.path,
      oldStr: o.old_str,
      newStr: typeof o.new_str === 'string' ? o.new_str : '',
    };
  }
  if (o.command === 'insert') {
    if (typeof o.insert_line !== 'number' || !Number.isInteger(o.insert_line)) throw new ParseErr(line);
    if (typeof o.new_str !== 'string') throw new ParseErr(line);
    return { command: 'insert', path: o.path, insertLine: o.insert_line, newStr: o.new_str };
  }
  throw new ParseErr(line);
}

function parseJson(lines: string[], patchText: string): EditFn[] {
  let first = -1;
  for (let i = 0; i < lines.length; i++) {
    if (!isBlank(lines[i])) {
      first = i;
      break;
    }
  }
  if (first === -1) throw new ParseErr(1);
  const firstChar = lines[first].trimStart()[0];
  const edits: JsonEdit[] = [];
  if (firstChar === '[') {
    const startLine = first + 1;
    let arr: unknown;
    try {
      arr = JSON.parse(patchText);
    } catch {
      throw new ParseErr(startLine);
    }
    if (!Array.isArray(arr)) throw new ParseErr(startLine);
    for (const item of arr) edits.push(validateJsonEdit(item, startLine));
    if (edits.length === 0) throw new ParseErr(1);
    return edits.map((e) => (tree: Tree) => applyJsonEdit(e, tree));
  }
  for (let i = 0; i < lines.length; i++) {
    const l = lines[i];
    if (isBlank(l)) continue;
    let obj: unknown;
    try {
      obj = JSON.parse(l);
    } catch {
      throw new ParseErr(i + 1);
    }
    edits.push(validateJsonEdit(obj, i + 1));
  }
  if (edits.length === 0) throw new ParseErr(1);
  return edits.map((e) => (tree: Tree) => applyJsonEdit(e, tree));
}

function countOverlapping(text: string, sub: string): { count: number; first: number } {
  let count = 0;
  let first = -1;
  let idx = 0;
  while (true) {
    const p = text.indexOf(sub, idx);
    if (p === -1) break;
    count += 1;
    if (first === -1) first = p;
    idx = p + 1;
    if (count > 1) break;
  }
  return { count, first };
}

function applyJsonEdit(e: JsonEdit, tree: Tree): Fail | null {
  if (!isSafe(e.path)) return { code: 'unsafe', path: e.path };
  if (e.command === 'create') {
    if (tree.existsAny(e.path)) return { code: 'exists', path: e.path };
    tree.set(e.path, e.fileText as string);
    return null;
  }
  if (e.command === 'str_replace') {
    if (!tree.existsFile(e.path)) return { code: 'missing', path: e.path };
    const cur = tree.getText(e.path);
    if (cur === null) return { code: 'missing', path: e.path };
    const f = splitFile(cur);
    let text: string;
    let oldS: string;
    let newS: string;
    if (f.brk === '\r\n') {
      text = cur.replace(/\r\n/g, '\n');
      oldS = (e.oldStr as string).replace(/\r\n/g, '\n');
      newS = (e.newStr as string).replace(/\r\n/g, '\n');
    } else {
      text = cur;
      oldS = e.oldStr as string;
      newS = e.newStr as string;
    }
    const found = countOverlapping(text, oldS);
    if (found.count === 0) return { code: 'no-match', path: e.path };
    if (found.count > 1) return { code: 'ambiguous', path: e.path };
    const result = text.slice(0, found.first) + newS + text.slice(found.first + oldS.length);
    tree.set(e.path, f.brk === '\r\n' ? result.replace(/\n/g, '\r\n') : result);
    return null;
  }
  // insert
  if (!tree.existsFile(e.path)) return { code: 'missing', path: e.path };
  const cur = tree.getText(e.path);
  if (cur === null) return { code: 'missing', path: e.path };
  const f = splitFile(cur);
  const at = e.insertLine as number;
  if (at < 0 || at > f.lines.length) return { code: 'no-match', path: e.path };
  const ins = e.newStr === '' ? [] : splitPatch(e.newStr as string);
  f.lines.splice(at, 0, ...ins);
  tree.set(e.path, joinFile(f));
  return null;
}

// ------------------------------------------------------- format detection

function detectFormat(lines: string[]): string | null {
  let firstNonBlank = -1;
  for (let i = 0; i < lines.length; i++) {
    if (!isBlank(lines[i])) {
      firstNonBlank = i;
      break;
    }
  }
  if (firstNonBlank === -1) return null;
  if (lines[firstNonBlank].trim() === '*** Begin Patch') return 'v4a';
  const firstChar = lines[firstNonBlank].trimStart()[0];
  if (firstChar === '[' || firstChar === '{') return 'json';
  for (const l of lines) {
    if (trimTrailST(l) === '<<<<<<< SEARCH') return 'search-replace';
  }
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].startsWith('diff --git ')) return 'unified';
    if (lines[i].startsWith('--- ') && i + 1 < lines.length && lines[i + 1].startsWith('+++ ')) return 'unified';
  }
  return null;
}

// ------------------------------------------------------------ CLI and output

interface CliArgs {
  format: string;
  check: boolean;
  strict: boolean;
  patch: string | null;
}

function parseArgs(argv: string[]): CliArgs | null {
  let format: string | null = null;
  let check = false;
  let strict = false;
  let patch: string | null = null;
  let positional = 0;
  let noMoreOptions = false;
  for (const arg of argv) {
    if (!noMoreOptions && arg === '--') {
      noMoreOptions = true;
      continue;
    }
    if (!noMoreOptions && arg.startsWith('-') && arg !== '-') {
      if (arg === '--check') {
        if (check) return null;
        check = true;
        continue;
      }
      if (arg === '--strict') {
        if (strict) return null;
        strict = true;
        continue;
      }
      if (arg.startsWith('--format=')) {
        if (format !== null) return null;
        const v = arg.slice('--format='.length);
        if (v !== 'unified' && v !== 'search-replace' && v !== 'v4a' && v !== 'json' && v !== 'auto') return null;
        format = v;
        continue;
      }
      return null;
    }
    positional += 1;
    if (positional > 1) return null;
    patch = arg;
  }
  return { format: format ?? 'auto', check, strict, patch };
}

interface ChangeEntry {
  sortKey: string;
  line: string;
}

function computeChanges(tree: Tree): { entries: ChangeEntry[]; writes: { path: string; after: string | undefined }[] } {
  const all = new Set<string>([...tree.initial.keys(), ...tree.state.keys()]);
  const entries: ChangeEntry[] = [];
  const writes: { path: string; after: string | undefined }[] = [];
  const supD = new Set<string>();
  const supA = new Set<string>();
  for (const m of tree.moves) {
    const oldBefore = tree.initial.has(m.old);
    const oldAfter = tree.state.has(m.old) ? tree.state.get(m.old) !== null : oldBefore;
    const newBefore = tree.initial.has(m.next);
    const newAfter = tree.state.has(m.next) ? tree.state.get(m.next) !== null : newBefore;
    if (oldBefore && !oldAfter && !newBefore && newAfter) {
      entries.push({ sortKey: m.next, line: `R ${m.old} -> ${m.next}` });
      supD.add(m.old);
      supA.add(m.next);
    }
  }
  for (const p of all) {
    const before = tree.initial.has(p) ? tree.initial.get(p) : undefined;
    let after: string | undefined;
    if (tree.state.has(p)) {
      const v = tree.state.get(p);
      after = v === null ? undefined : v;
    } else {
      after = before;
    }
    if (before === after) continue;
    writes.push({ path: p, after });
    if (before === undefined && after !== undefined) {
      if (!supA.has(p)) entries.push({ sortKey: p, line: `A ${p}` });
    } else if (before !== undefined && after === undefined) {
      if (!supD.has(p)) entries.push({ sortKey: p, line: `D ${p}` });
    } else {
      entries.push({ sortKey: p, line: `M ${p}` });
    }
  }
  entries.sort((a, b) => Buffer.compare(Buffer.from(a.sortKey, 'utf8'), Buffer.from(b.sortKey, 'utf8')));
  return { entries, writes };
}

function writeChanges(writes: { path: string; after: string | undefined }[]): void {
  for (const w of writes) {
    if (w.after === undefined) {
      try {
        rmSync(w.path, { force: true });
      } catch {
        // best effort: the path is gone from the tree either way
      }
    } else {
      const dir = dirname(w.path);
      if (dir !== '' && dir !== '.') mkdirSync(dir, { recursive: true });
      writeFileSync(w.path, w.after, 'utf8');
    }
  }
}

function failExit2(msg: string): void {
  process.stdout.write(`${msg}\n`);
  process.exitCode = 2;
}

function main(): void {
  const parsed = parseArgs(process.argv.slice(2));
  if (parsed === null) {
    failExit2('error: usage');
    return;
  }
  let patchText: string;
  if (parsed.patch === null || parsed.patch === '-') {
    patchText = readFileSync(0, 'utf8');
  } else {
    try {
      patchText = readFileSync(parsed.patch, 'utf8');
    } catch {
      failExit2('error: no-patch');
      return;
    }
  }
  const lines = splitPatch(patchText);
  let fmt = parsed.format;
  if (fmt === 'auto') {
    const detected = detectFormat(lines);
    if (detected === null) {
      failExit2('error: format');
      return;
    }
    fmt = detected;
  }
  let edits: EditFn[];
  try {
    if (fmt === 'unified') edits = parseUnified(lines);
    else if (fmt === 'search-replace') edits = parseSearchReplace(lines);
    else if (fmt === 'v4a') edits = parseV4A(lines);
    else edits = parseJson(lines, patchText);
  } catch (err) {
    if (err instanceof ParseErr) {
      failExit2(`error: parse ${err.line}`);
      return;
    }
    throw err;
  }
  const tree = new Tree();
  const failures: Fail[] = [];
  for (const edit of edits) {
    const f = edit(tree, parsed.strict);
    if (f !== null) failures.push(f);
  }
  if (failures.length > 0) {
    const out: string[] = [];
    for (const f of failures) out.push(`error: ${f.code} ${f.path}`);
    out.push(`failed: ${failures.length} of ${edits.length} edits`);
    process.stdout.write(`${out.join('\n')}\n`);
    process.exitCode = 1;
    return;
  }
  const changes = computeChanges(tree);
  if (!parsed.check) writeChanges(changes.writes);
  const out: string[] = [];
  for (const c of changes.entries) out.push(c.line);
  out.push(`ok: ${changes.entries.length} ${changes.entries.length === 1 ? 'file' : 'files'}`);
  process.stdout.write(`${out.join('\n')}\n`);
  process.exitCode = 0;
}

// ------------------------------------------------------------ trial hand-over

const envUrl = process.env.MAKEFUN_ENV_URL;
if (envUrl !== undefined && envUrl !== '') {
  runTrial(envUrl).then(
    () => {
      process.exit(0);
    },
    (err: unknown) => {
      process.stderr.write(`runTrial failed: ${err instanceof Error ? (err.stack ?? err.message) : String(err)}\n`);
      process.exit(1);
    },
  );
} else {
  main();
}
