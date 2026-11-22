// main.ts is mend, the CLI SPEC.md specifies. Node 22, the standard library alone; run it as
// `node main.ts [options] [PATCH]`. It reads a patch in one of four formats (unified diff,
// SEARCH/REPLACE blocks, V4A patches, JSON edits), finds the lines each edit names at the first of
// three matching tiers, and writes every change or none, printing what it changed or why it failed.
//
// In a trial the grader runs `node /bot/main.ts` with MAKEFUN_ENV_URL set, and then this file hands
// over to runner.ts (the last lines below): keep that hand-over and runner.ts as they are.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** One file's lines, its line break, and whether its text ends with that break (SPEC.md section 3). */
interface FileView {
  br: string;
  lines: string[];
  final: boolean;
}

function splitFile(text: string): FileView {
  if (text === '') return { br: '\n', lines: [], final: false };
  const nl = text.indexOf('\n');
  const br = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const final = text.endsWith(br);
  const parts = text.split(br);
  if (final) parts.pop();
  return { br, lines: parts, final };
}

function joinFile(v: FileView): string {
  if (v.lines.length === 0) return '';
  return v.lines.join(v.br) + (v.final ? v.br : '');
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type EditResult = { move?: [string, string] } | void;
type Edit = (tree: Tree) => EditResult;

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One body line of a hunk or chunk: context, old (`-`) or new (`+`). `bs` is set when a `\` line
 *  (as in `\ No newline at end of file`) follows this line in the patch body. */
interface BLine {
  kind: 'ctx' | 'del' | 'add';
  text: string;
  bs: boolean;
}

function leadWs(s: string): string {
  const m = /^[ \t]*/.exec(s);
  return m ? m[0] : '';
}

function trimEndWs(s: string): string {
  return s.replace(/[ \t]+$/, '');
}

function trimBothWs(s: string): string {
  return s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

/** A line as a tier reads it: tier 0 exact, tier 1 without trailing spaces and tabs, tier 2
 *  without leading and trailing spaces and tabs (SPEC.md section 5). */
function normLine(s: string, tier: number): string {
  return tier === 0 ? s : tier === 1 ? trimEndWs(s) : trimBothWs(s);
}

/** Every 0-based position where O occurs in the file's lines at one tier; occurrences may overlap. */
function occurrences(fileLines: string[], o: string[], tier: number): number[] {
  const nO = o.map((s) => normLine(s, tier));
  const nF = fileLines.map((s) => normLine(s, tier));
  const out: number[] = [];
  for (let i = 0; i + o.length <= fileLines.length; i++) {
    let ok = true;
    for (let j = 0; j < o.length; j++) {
      if (nF[i + j] !== nO[j]) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/** The first tier at which O occurs at least once, with its occurrences; null when it occurs at no
 *  tier. With --strict only tier 0 is tried. */
function findOccurrences(fileLines: string[], o: string[], strict: boolean): { tier: number; occ: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const occ = occurrences(fileLines, o, t);
    if (occ.length > 0) return { tier: t, occ };
  }
  return null;
}

/** The first tier at which O occurs at or after `from`, with its occurrences; for an end-of-file
 *  chunk only occurrences that end at the file's last line count. */
function findOccurrencesFrom(
  fileLines: string[],
  o: string[],
  from: number,
  eof: boolean,
  strict: boolean,
): { tier: number; occ: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const occ: number[] = [];
    for (let i = from; i + o.length <= fileLines.length; i++) {
      if (eof && i + o.length !== fileLines.length) continue;
      let ok = true;
      for (let j = 0; j < o.length; j++) {
        if (normLine(fileLines[i + j]!, t) !== normLine(o[j]!, t)) {
          ok = false;
          break;
        }
      }
      if (ok) occ.push(i);
    }
    if (occ.length > 0) return { tier: t, occ };
  }
  return null;
}

/** The lines N writes in place of the matched lines. A context line is written as the file's own
 *  matched line, never the patch's. At tier 2 every other line of N is re-indented: F is the leading
 *  spaces and tabs of the file's first matched line, P those of O's first line, and a line that
 *  starts with P has that P replaced by F; any other non-blank line keeps its own leading whitespace
 *  after F. At tiers 0 and 1 the lines of N are written as they are. */
function buildNew(fileLines: string[], at: number, tier: number, o: BLine[], n: BLine[]): string[] {
  const ctxFile: string[] = [];
  o.forEach((e, k) => {
    if (e.kind === 'ctx') ctxFile.push(fileLines[at + k]!);
  });
  const P = o.length > 0 ? leadWs(o[0]!.text) : '';
  const F = leadWs(fileLines[at] ?? '');
  let ci = 0;
  const out: string[] = [];
  for (const e of n) {
    if (e.kind === 'ctx') {
      out.push(ctxFile[ci++]!);
      continue;
    }
    let t = e.text;
    if (tier === 2 && t !== '' && !/^[ \t]*$/.test(t)) {
      t = F + (t.startsWith(P) ? t.slice(P.length) : t);
    }
    out.push(t);
  }
  return out;
}

function replaceAt(lines: string[], at: number, len: number, repl: string[]): string[] {
  return [...lines.slice(0, at), ...repl, ...lines.slice(at + len)];
}

// ---------------------------------------------------------------------------
// Section 6: unified diffs.
// ---------------------------------------------------------------------------

interface Hunk {
  A: number;
  entries: BLine[];
  bsAfterLast: boolean;
}

interface UniSection {
  oldPath: string | null; // null means /dev/null: no file
  newPath: string | null;
  pairSet: boolean;
  create: boolean;
  del: boolean;
  hunks: Hunk[];
}

/** The path a `--- ` or `+++ ` line names: the text after the four characters, up to the first
 *  tab, with surrounding spaces removed, and one leading `a/` or `b/` removed. */
function unifiedPath(line: string): string {
  let p = line.slice(4);
  const tab = p.indexOf('\t');
  if (tab >= 0) p = p.slice(0, tab);
  p = p.trim();
  if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice(2);
  return p;
}

const DIFF_GIT = /^diff --git a\/(\S+) b\/(\S+)$/;
const HUNK_HEAD = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/;

/** Split the patch into sections with their hunks (SPEC.md section 6). */
function parseUnified(lines: string[]): UniSection[] {
  const sections: UniSection[] = [];
  let cur: UniSection | null = null;
  let inHeader = false;
  let hunk: Hunk | null = null;
  let body: string[] = [];

  const endBody = (): void => {
    if (hunk === null) return;
    while (body.length > 0 && body[body.length - 1] === '') body.pop();
    const entries: BLine[] = [];
    for (const raw of body) {
      if (raw.startsWith('\\')) {
        if (entries.length > 0) entries[entries.length - 1]!.bs = true;
        continue;
      }
      const kind = raw === '' || raw[0] === ' ' ? 'ctx' : raw[0] === '-' ? 'del' : 'add';
      entries.push({ kind, text: raw === '' ? '' : raw.slice(1), bs: false });
    }
    hunk.entries = entries;
    let last: BLine | null = null;
    for (const e of entries) if (e.kind !== 'del') last = e;
    hunk.bsAfterLast = last !== null && last.bs;
    body = [];
    hunk = null;
  };

  for (let j = 0; j < lines.length; j++) {
    const line = lines[j]!;
    if (hunk !== null) {
      if (line.startsWith('diff --git ')) {
        endBody();
      } else if (line.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) {
        endBody();
      } else if (line === '' || line[0] === ' ' || line[0] === '-' || line[0] === '+' || line[0] === '\\') {
        body.push(line);
        continue;
      } else {
        endBody();
      }
    }
    if (line.startsWith('diff --git ')) {
      const m = DIFF_GIT.exec(line);
      if (m === null) throw new Exit2(`error: parse ${j + 1}`);
      cur = { oldPath: m[1]!, newPath: m[2]!, pairSet: false, create: false, del: false, hunks: [] };
      sections.push(cur);
      inHeader = true;
      continue;
    }
    if (line.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) {
      const oldP = unifiedPath(line);
      const newP = unifiedPath(lines[j + 1]!);
      if (cur !== null && inHeader && !cur.pairSet) {
        cur.oldPath = oldP === '/dev/null' ? null : oldP;
        cur.newPath = newP === '/dev/null' ? null : newP;
        cur.pairSet = true;
        j++;
        continue;
      }
      cur = {
        oldPath: oldP === '/dev/null' ? null : oldP,
        newPath: newP === '/dev/null' ? null : newP,
        pairSet: true,
        create: false,
        del: false,
        hunks: [],
      };
      sections.push(cur);
      inHeader = true;
      j++;
      continue;
    }
    if (line.startsWith('--- ')) {
      if (cur !== null && inHeader) throw new Exit2(`error: parse ${j + 2}`);
      continue;
    }
    if (line.startsWith('@@')) {
      const m = HUNK_HEAD.exec(line);
      if (m === null) throw new Exit2(`error: parse ${j + 1}`);
      if (cur === null) throw new Exit2(`error: parse ${j + 1}`);
      hunk = { A: Number(m[1]), entries: [], bsAfterLast: false };
      cur.hunks.push(hunk);
      inHeader = false;
      body = [];
      continue;
    }
    if (cur !== null && inHeader) {
      if (line.startsWith('rename from ')) {
        if (!cur.pairSet) cur.oldPath = line.slice('rename from '.length).trim();
      } else if (line.startsWith('rename to ')) {
        if (!cur.pairSet) cur.newPath = line.slice('rename to '.length).trim();
      } else if (line.startsWith('new file mode')) {
        cur.create = true;
      } else if (line.startsWith('deleted file mode')) {
        cur.del = true;
      }
      continue;
    }
    // Outside bodies, lines that are not part of a section header are ignored (prose, code fences).
  }
  endBody();
  return sections;
}

/** Apply one hunk to a file view. `d` is the sum over this section's hunks applied so far of
 *  (N's length minus O's length). */
function applyHunk(view: FileView, hunk: Hunk, d: number, strict: boolean, path: string): FileView {
  const o = hunk.entries.filter((e) => e.kind !== 'add');
  const n = hunk.entries.filter((e) => e.kind !== 'del');
  const oTexts = o.map((e) => e.text);
  let lines = view.lines;
  let final = view.final;
  if (oTexts.length === 0) {
    const pos = Math.min(hunk.A + d, lines.length);
    lines = replaceAt(lines, pos, 0, n.map((e) => e.text));
    if (pos === view.lines.length) final = !hunk.bsAfterLast;
    return { br: view.br, lines, final };
  }
  const found = findOccurrences(lines, oTexts, strict);
  if (found === null) throw new Fail('no-match', path);
  const target = hunk.A - 1 + d;
  let best = found.occ[0]!;
  for (const p of found.occ) {
    if (Math.abs(p - target) < Math.abs(best - target)) best = p;
  }
  const repl = buildNew(lines, best, found.tier, o, n);
  lines = replaceAt(lines, best, oTexts.length, repl);
  if (best + oTexts.length === view.lines.length) final = !hunk.bsAfterLast;
  return { br: view.br, lines, final };
}

function applySectionHunks(text: string, sec: UniSection, strict: boolean, path: string): string {
  let view = splitFile(text);
  let d = 0;
  for (const hunk of sec.hunks) {
    view = applyHunk(view, hunk, d, strict, path);
    const oLen = hunk.entries.filter((e) => e.kind !== 'add').length;
    const nLen = hunk.entries.filter((e) => e.kind !== 'del').length;
    d += nLen - oLen;
  }
  return joinFile(view);
}

function makeUnifiedEdit(sec: UniSection, strict: boolean): Edit {
  const oldP = sec.oldPath;
  const newP = sec.newPath;
  const isCreate = sec.create || oldP === null;
  const isDelete = !isCreate && (sec.del || newP === null);
  const isMove = !isCreate && !isDelete && oldP !== null && newP !== null && oldP !== newP;
  return (tree) => {
    const named: string[] = [];
    if (oldP !== null) named.push(oldP);
    if (newP !== null && newP !== oldP) named.push(newP);
    for (const p of named) {
      if (!safe(p)) throw new Fail('unsafe', p);
    }
    if (isCreate) {
      const np = newP ?? '/dev/null';
      if (!safe(np)) throw new Fail('unsafe', np);
      if (tree.get(np) !== null) throw new Fail('exists', np);
      let lastPlus: BLine | null = null;
      const plus: string[] = [];
      for (const h of sec.hunks) {
        for (const e of h.entries) {
          if (e.kind === 'add') {
            plus.push(e.text);
            lastPlus = e;
          }
        }
      }
      const text = plus.length === 0 ? '' : plus.join('\n') + (lastPlus !== null && lastPlus.bs ? '' : '\n');
      tree.now.set(np, text);
      return undefined;
    }
    if (isDelete) {
      const op = oldP ?? '/dev/null';
      if (tree.get(op) === null) throw new Fail('missing', op);
      tree.now.set(op, null);
      return undefined;
    }
    if (isMove) {
      const op = oldP!;
      const np = newP!;
      if (tree.get(op) === null) throw new Fail('missing', op);
      if (tree.get(np) !== null) throw new Fail('exists', np);
      const content = applySectionHunks(tree.get(op)!, sec, strict, op);
      tree.now.set(np, content);
      tree.now.set(op, null);
      return { move: [op, np] };
    }
    const p = oldP ?? newP!;
    if (tree.get(p) === null) throw new Fail('missing', p);
    tree.now.set(p, applySectionHunks(tree.get(p)!, sec, strict, p));
    return undefined;
  };
}

function unifiedEdits(lines: string[], strict: boolean): Edit[] {
  return parseUnified(lines).map((sec) => makeUnifiedEdit(sec, strict));
}

// ---------------------------------------------------------------------------
// Section 7: SEARCH/REPLACE blocks.
// ---------------------------------------------------------------------------

interface SRBlock {
  path: string;
  oldLines: string[];
  newLines: string[];
}

/** Split the patch into its SEARCH/REPLACE blocks (SPEC.md section 7). */
function parseSR(lines: string[]): SRBlock[] {
  const blocks: SRBlock[] = [];
  let prevEnd = -1;
  let prevPath: string | null = null;
  let j = 0;
  while (j < lines.length) {
    if (lines[j]!.trimEnd() !== '<<<<<<< SEARCH') {
      j++;
      continue;
    }
    const sIdx = j;
    let eq = -1;
    for (let k = sIdx + 1; k < lines.length; k++) {
      if (lines[k]!.trimEnd() === '=======') {
        eq = k;
        break;
      }
    }
    if (eq < 0) throw new Exit2(`error: parse ${sIdx + 1}`);
    let rep = -1;
    for (let k = eq + 1; k < lines.length; k++) {
      if (lines[k]!.trimEnd() === '>>>>>>> REPLACE') {
        rep = k;
        break;
      }
    }
    if (rep < 0) throw new Exit2(`error: parse ${sIdx + 1}`);
    let path: string | null = null;
    for (let k = sIdx - 1; k > prevEnd; k--) {
      const l = lines[k]!;
      if (blank(l)) continue;
      if (l.trim().startsWith('```')) continue;
      path = l.trim();
      break;
    }
    if (path === null) {
      if (prevPath === null) throw new Exit2(`error: parse ${sIdx + 1}`);
      path = prevPath;
    }
    blocks.push({ path, oldLines: lines.slice(sIdx + 1, eq), newLines: lines.slice(eq + 1, rep) });
    prevPath = path;
    prevEnd = rep;
    j = rep + 1;
  }
  return blocks;
}

function makeSREdit(b: SRBlock, strict: boolean): Edit {
  return (tree) => {
    const p = b.path;
    if (!safe(p)) throw new Fail('unsafe', p);
    if (b.oldLines.length === 0) {
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, b.newLines.length === 0 ? '' : b.newLines.join('\n') + '\n');
      return undefined;
    }
    const cur = tree.get(p);
    if (cur === null) throw new Fail('missing', p);
    const view = splitFile(cur);
    const found = findOccurrences(view.lines, b.oldLines, strict);
    if (found === null) throw new Fail('no-match', p);
    if (found.occ.length > 1) throw new Fail('ambiguous', p);
    const at = found.occ[0]!;
    const o: BLine[] = b.oldLines.map((t) => ({ kind: 'del' as const, text: t, bs: false }));
    const n: BLine[] = b.newLines.map((t) => ({ kind: 'add' as const, text: t, bs: false }));
    const repl = buildNew(view.lines, at, found.tier, o, n);
    const lines = replaceAt(view.lines, at, b.oldLines.length, repl);
    tree.now.set(p, joinFile({ br: view.br, lines, final: view.final }));
    return undefined;
  };
}

function srEdits(lines: string[], strict: boolean): Edit[] {
  return parseSR(lines).map((b) => makeSREdit(b, strict));
}

// ---------------------------------------------------------------------------
// Section 8: V4A patches.
// ---------------------------------------------------------------------------

interface V4AChunk {
  anchor: string | null;
  eof: boolean;
  entries: BLine[];
}

interface V4ASection {
  kind: 'add' | 'delete' | 'update';
  path: string;
  moveTo: string | null;
  lines: string[]; // Add File: the file's lines
  chunks: V4AChunk[]; // Update File: its chunks
  updateLine: number; // 1-based line of the Update File line
}

function isV4ASectionStart(l: string): boolean {
  return l.startsWith('*** Add File: ') || l.startsWith('*** Delete File: ') || l.startsWith('*** Update File: ');
}

/** Split the patch into its sections (SPEC.md section 8). */
function parseV4A(lines: string[]): V4ASection[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = lines.length - 1;
  while (last >= 0 && blank(lines[last]!)) last--;
  if (last < 0 || lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const sections: V4ASection[] = [];
  let i = first + 1;
  while (i < last) {
    const line = lines[i]!;
    if (blank(line)) {
      i++;
      continue;
    }
    if (line.startsWith('*** Add File: ')) {
      const path = line.slice('*** Add File: '.length).trim();
      const raw: string[] = [];
      i++;
      while (i < last && !isV4ASectionStart(lines[i]!)) {
        const l = lines[i]!;
        if (l === '' || l.startsWith('+')) raw.push(l);
        else if (blank(l)) raw.push('');
        else throw new Exit2(`error: parse ${i + 1}`);
        i++;
      }
      while (raw.length > 0 && raw[raw.length - 1] === '') raw.pop();
      sections.push({ kind: 'add', path, moveTo: null, lines: raw.map((l) => (l === '' ? '' : l.slice(1))), chunks: [], updateLine: 0 });
      continue;
    }
    if (line.startsWith('*** Delete File: ')) {
      const path = line.slice('*** Delete File: '.length).trim();
      i++;
      while (i < last && !isV4ASectionStart(lines[i]!)) {
        if (blank(lines[i]!)) {
          i++;
          continue;
        }
        throw new Exit2(`error: parse ${i + 1}`);
      }
      sections.push({ kind: 'delete', path, moveTo: null, lines: [], chunks: [], updateLine: 0 });
      continue;
    }
    if (line.startsWith('*** Update File: ')) {
      const path = line.slice('*** Update File: '.length).trim();
      const updateLine = i + 1;
      i++;
      let moveTo: string | null = null;
      if (i < last && lines[i]!.startsWith('*** Move to: ')) {
        moveTo = lines[i]!.slice('*** Move to: '.length).trim();
        i++;
      }
      const chunks: V4AChunk[] = [];
      let cur: V4AChunk | null = null;
      let started = false;
      const endChunk = (): void => {
        if (cur !== null) {
          chunks.push(cur);
          cur = null;
        }
      };
      while (i < last) {
        const l = lines[i]!;
        if (isV4ASectionStart(l)) break;
        if (l.startsWith('@@')) {
          endChunk();
          const anchor = l.slice(2).trim();
          cur = { anchor: anchor === '' ? null : anchor, eof: false, entries: [] };
          started = true;
          i++;
          continue;
        }
        if (l.trim() === '*** End of File' && !l.startsWith(' ') && !l.startsWith('-') && !l.startsWith('+')) {
          if (cur === null) {
            cur = { anchor: null, eof: true, entries: [] };
            started = true;
          } else {
            cur.eof = true;
          }
          endChunk();
          i++;
          continue;
        }
        if (l === '' || l[0] === ' ' || l[0] === '-' || l[0] === '+') {
          if (cur === null) {
            if (!started) {
              cur = { anchor: null, eof: false, entries: [] };
              started = true;
            } else {
              throw new Exit2(`error: parse ${i + 1}`);
            }
          }
          const kind = l === '' || l[0] === ' ' ? 'ctx' : l[0] === '-' ? 'del' : 'add';
          cur.entries.push({ kind, text: l === '' ? '' : l.slice(1), bs: false });
          i++;
          continue;
        }
        throw new Exit2(`error: parse ${i + 1}`);
      }
      endChunk();
      // Blank lines at the end of a section are not part of it: drop trailing empty context
      // lines from the section's last chunk.
      if (chunks.length > 0) {
        const lastChunk = chunks[chunks.length - 1]!;
        while (lastChunk.entries.length > 0) {
          const e = lastChunk.entries[lastChunk.entries.length - 1]!;
          if (e.kind === 'ctx' && e.text === '') lastChunk.entries.pop();
          else break;
        }
      }
      if (chunks.length === 0 && moveTo === null) throw new Exit2(`error: parse ${updateLine}`);
      sections.push({ kind: 'update', path, moveTo, lines: [], chunks, updateLine });
      continue;
    }
    throw new Exit2(`error: parse ${i + 1}`);
  }
  return sections;
}

/** The first line at or after the cursor equal to the anchor, at the first tier where one is. */
function findAnchorLine(lines: string[], anchor: string, from: number, strict: boolean): number {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    for (let i = from; i < lines.length; i++) {
      if (normLine(lines[i]!, t) === normLine(anchor, t)) return i;
    }
  }
  return -1;
}

function applyV4AUpdate(text: string, sec: V4ASection, strict: boolean): string {
  let view = splitFile(text);
  let cursor = 0;
  for (const chunk of sec.chunks) {
    if (chunk.anchor !== null) {
      const idx = findAnchorLine(view.lines, chunk.anchor, cursor, strict);
      if (idx < 0) throw new Fail('no-match', sec.path);
      cursor = idx + 1;
    }
    const o = chunk.entries.filter((e) => e.kind !== 'add');
    const n = chunk.entries.filter((e) => e.kind !== 'del');
    const oTexts = o.map((e) => e.text);
    if (oTexts.length === 0) {
      const pos = chunk.eof ? view.lines.length : cursor;
      const lines = replaceAt(view.lines, pos, 0, n.map((e) => e.text));
      view = { br: view.br, lines, final: view.final };
      cursor = pos + n.length;
      continue;
    }
    const found = findOccurrencesFrom(view.lines, oTexts, cursor, chunk.eof, strict);
    if (found === null) throw new Fail('no-match', sec.path);
    const at = found.occ[0]!;
    const repl = buildNew(view.lines, at, found.tier, o, n);
    const lines = replaceAt(view.lines, at, oTexts.length, repl);
    view = { br: view.br, lines, final: view.final };
    cursor = at + repl.length;
  }
  return joinFile(view);
}

function makeV4AEdit(sec: V4ASection, strict: boolean): Edit {
  return (tree) => {
    const p = sec.path;
    if (!safe(p)) throw new Fail('unsafe', p);
    if (sec.kind === 'add') {
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, sec.lines.length === 0 ? '' : sec.lines.join('\n') + '\n');
      return undefined;
    }
    if (sec.kind === 'delete') {
      if (tree.get(p) === null) throw new Fail('missing', p);
      tree.now.set(p, null);
      return undefined;
    }
    if (sec.moveTo !== null && !safe(sec.moveTo)) throw new Fail('unsafe', sec.moveTo);
    const cur = tree.get(p);
    if (cur === null) throw new Fail('missing', p);
    if (sec.moveTo !== null && tree.get(sec.moveTo) !== null) throw new Fail('exists', sec.moveTo);
    const content = applyV4AUpdate(cur, sec, strict);
    if (sec.moveTo !== null) {
      tree.now.set(sec.moveTo, content);
      tree.now.set(p, null);
      return { move: [p, sec.moveTo] };
    }
    tree.now.set(p, content);
    return undefined;
  };
}

function v4aEdits(lines: string[], strict: boolean): Edit[] {
  return parseV4A(lines).map((sec) => makeV4AEdit(sec, strict));
}

// ---------------------------------------------------------------------------
// Section 9: JSON edits.
// ---------------------------------------------------------------------------

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

// ---------------------------------------------------------------------------
// Section 10: order and atomicity; sections 1 and 2: invocation, output.
// ---------------------------------------------------------------------------

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  let edits: Edit[];
  try {
    edits =
      kind === 'json'
        ? jsonEdits(text, lines)
        : kind === 'unified'
          ? unifiedEdits(lines, strict)
          : kind === 'search-replace'
            ? srEdits(lines, strict)
            : v4aEdits(lines, strict);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  const moves: Array<[string, string]> = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      const r = edit(tree);
      if (r !== undefined && r.move !== undefined) moves.push(r.move);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  const byteOrder = (a: string, b: string): number => Buffer.compare(Buffer.from(a), Buffer.from(b));
  const rows: { key: string; text: string }[] = [];
  const suppressed = new Set<string>();
  for (const [oldP, newP] of moves) {
    if (tree.original(oldP) !== null && tree.get(oldP) === null && tree.original(newP) === null && tree.get(newP) !== null) {
      rows.push({ key: newP, text: `R ${oldP} -> ${newP}` });
      suppressed.add(oldP);
      suppressed.add(newP);
    }
  }
  for (const p of [...tree.now.keys()].sort(byteOrder)) {
    if (suppressed.has(p)) continue;
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    rows.push({ key: p, text: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  if (!check) {
    for (const p of [...tree.now.keys()]) {
      const was = tree.original(p);
      const now = tree.now.get(p)!;
      if (was === now) continue;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  rows.sort((a, b) => byteOrder(a.key, b.key));
  const out = rows.map((r) => r.text);
  return { code: 0, out: [...out, `ok: ${out.length} ${out.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
