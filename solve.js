// Drop-in replacement for makefun-diff 1.0.0: greedy Myers line diff with the
// exact makefun-diff/1 patch format. Dependency-free, deterministic.
// SPDX-License-Identifier: MIT
//
// Speed notes: every distinct line is interned once to an integer id (one
// shared Map for old+new; a terminated line "abc\n" and the unterminated
// "abc" are different Map keys, so they never share an id), so the hot
// Myers/snake loops compare ints, never strings. The full V history lives
// in one flat Int32Array (row d at offset d*(d+1)/2, d+1 entries) so
// backtracking needs no re-computation.

export function run(input) {
  const oldText = input.old;
  const newText = input.new;

  if (oldText === newText) {
    const n = countLines(oldText);
    return `makefun-diff/1 old=${n} new=${n} hunks=0 deleted=0 inserted=0\n`;
  }

  // Interning table: id -> line string (kept for patch output).
  const strs = [];
  const ids = new Map();
  const intern = (s) => {
    let id = ids.get(s);
    if (id === undefined) {
      id = strs.length;
      strs.push(s);
      ids.set(s, id);
    }
    return id;
  };

  const a = tokenize(oldText, intern);
  const b = tokenize(newText, intern);
  const N = a.length;
  const M = b.length;

  // Longest common prefix / suffix of lines.
  let pre = 0;
  const minNM = N < M ? N : M;
  while (pre < minNM && a[pre] === b[pre]) pre++;
  let suf = 0;
  while (suf < minNM - pre && a[N - 1 - suf] === b[M - 1 - suf]) suf++;

  const n2 = N - pre - suf;
  const m2 = M - pre - suf;

  // Ops over the whole text: kind 0=KEEP, 1=DELETE, 2=INSERT; oi/ni are
  // line indexes into a/b (-1 when the op does not touch that side).
  const kinds = [];
  const ois = [];
  const nis = [];
  const push = (k, oi, ni) => {
    kinds.push(k);
    ois.push(oi);
    nis.push(ni);
  };

  for (let i = 0; i < pre; i++) push(0, i, i);

  if (n2 === 0 && m2 === 0) {
    // Nothing in the middle: all keeps (handled by prefix+suffix below).
  } else if (n2 === 0) {
    for (let j = 0; j < m2; j++) push(2, -1, pre + j);
  } else if (m2 === 0) {
    for (let i = 0; i < n2; i++) push(1, pre + i, -1);
  } else {
    const mid = myers(a.subarray(pre, N - suf), b.subarray(pre, M - suf));
    for (let t = 0; t < mid.kinds.length; t++) {
      const k = mid.kinds[t];
      push(k, k === 2 ? -1 : pre + mid.ois[t], k === 1 ? -1 : pre + mid.nis[t]);
    }
  }

  for (let i = 0; i < suf; i++) push(0, N - suf + i, M - suf + i);

  return formatPatch(a, b, strs, kinds, ois, nis, N, M);
}

function countLines(text) {
  if (text === '') return 0;
  let n = 0;
  let at = -1;
  for (;;) {
    at = text.indexOf('\n', at + 1);
    if (at === -1) break;
    n++;
  }
  // A trailing "\n" ends the last line; otherwise there is one more line.
  return text.charCodeAt(text.length - 1) === 10 ? n : n + 1;
}

// Split after every "\n" ("\r" stays part of the line). The last part, when
// non-empty, is one unterminated line. Empty text has zero lines.
function tokenize(text, intern) {
  const parts = text.split('\n');
  const last = parts.length - 1;
  const hasLast = parts[last] !== '';
  const n = last + (hasLast ? 1 : 0);
  const out = new Int32Array(n);
  for (let i = 0; i < last; i++) out[i] = intern(parts[i] + '\n');
  if (hasLast) out[last] = intern(parts[last]);
  return out;
}

// Greedy Myers over the middle slices. Returns forward-order ops with
// indexes relative to the slices. Full V history is kept in one flat
// Int32Array: row d starts at d*(d+1)/2 and holds d+1 entries, entry
// (k+d)/2 being V[d][k] (x after the snake), or -1 when unreachable.
function myers(a, b) {
  const N = a.length;
  const M = b.length;
  const off = (d) => (d * (d + 1)) >> 1;

  let cap = 1 << 20;
  let hist = new Int32Array(cap);
  const ensure = (need) => {
    if (need <= cap) return;
    let nc = cap;
    while (nc < need) nc <<= 1;
    const nh = new Int32Array(nc);
    nh.set(hist);
    hist = nh;
    cap = nc;
  };

  let D = -1;
  // d = 0: x = 0, then the snake.
  let x = 0;
  let y = 0;
  while (x < N && y < M && a[x] === b[y]) {
    x++;
    y++;
  }
  hist[0] = x;
  if (x === N && y === M) {
    D = 0;
  } else {
    outer: for (let d = 1; d <= N + M; d++) {
      ensure(off(d) + d + 1);
      const base = off(d);
      const prevBase = off(d - 1);
      for (let k = -d; k <= d; k += 2) {
        let xx = -1;
        if (k === -d) {
          // Insertion only: one new line past V[d-1][k+1].
          const v = hist[prevBase + ((k + 1 + d - 1) >> 1)];
          if (v >= 0 && v - k <= M) xx = v;
        } else if (k === d) {
          // Deletion only: one old line past V[d-1][k-1].
          const v = hist[prevBase + ((k - 1 + d - 1) >> 1)];
          if (v >= 0 && v + 1 <= N) xx = v + 1;
        } else {
          const vDel = hist[prevBase + ((k - 1 + d - 1) >> 1)];
          const vIns = hist[prevBase + ((k + 1 + d - 1) >> 1)];
          const delX = vDel >= 0 && vDel + 1 <= N ? vDel + 1 : -1;
          const insX = vIns >= 0 && vIns - k <= M ? vIns : -1;
          // Farthest into old wins; ties go to DELETION.
          xx = delX >= insX ? delX : insX;
        }
        if (xx >= 0) {
          let yy = xx - k;
          while (xx < N && yy < M && a[xx] === b[yy]) {
            xx++;
            yy++;
          }
        }
        hist[base + ((k + d) >> 1)] = xx;
        if (xx === N && xx - k === M) {
          D = d;
          break outer;
        }
      }
    }
  }

  // Backtrack from (D, k = N-M, x = N) to (0, 0, 0), collecting ops reversed.
  const kinds = [];
  const ois = [];
  const nis = [];
  let k = N - M;
  x = N;
  const getV = (d, kk) => hist[off(d) + ((kk + d) >> 1)];
  for (let d = D; d >= 1; d--) {
    let delX = -1;
    let insX = -1;
    if (k - 1 >= -(d - 1) && k - 1 <= d - 1) {
      const v = getV(d - 1, k - 1);
      if (v >= 0 && v + 1 <= N) delX = v + 1;
    }
    if (k + 1 >= -(d - 1) && k + 1 <= d - 1) {
      const v = getV(d - 1, k + 1);
      if (v >= 0 && v - k <= M) insX = v;
    }
    if (delX < 0 && insX < 0) throw new Error('myers backtrack: no valid predecessor');
    const isDel = delX >= insX; // ties (and del-only) go to DELETION
    const prevK = isDel ? k - 1 : k + 1;
    const prevX = getV(d - 1, prevK);
    const prevY = prevX - prevK;
    const curX = getV(d, k);
    // Snake keeps on diagonal k, from just after the edit step to (curX, curY).
    const sx = isDel ? prevX + 1 : prevX;
    for (let i = curX - 1; i >= sx; i--) {
      kinds.push(0);
      ois.push(i);
      nis.push(i - k);
    }
    if (isDel) {
      kinds.push(1);
      ois.push(prevX);
      nis.push(-1);
    } else {
      kinds.push(2);
      ois.push(-1);
      nis.push(prevY);
    }
    k = prevK;
    x = prevX;
  }
  // Row 0 snake keeps from (0,0) to (x,x).
  for (let i = x - 1; i >= 0; i--) {
    kinds.push(0);
    ois.push(i);
    nis.push(i);
  }
  kinds.reverse();
  ois.reverse();
  nis.reverse();
  return { kinds, ois, nis };
}

// Patch format: header line, then hunks with 3 lines of context; runs at
// most 6 kept lines apart share one hunk. Inside a change run, deletions
// come before insertions. An unterminated line is written with an added
// newline followed by a "%" line.
function formatPatch(a, b, strs, kinds, ois, nis, N, M) {
  const total = kinds.length;
  let deleted = 0;
  let inserted = 0;
  for (let i = 0; i < total; i++) {
    if (kinds[i] === 1) deleted++;
    else if (kinds[i] === 2) inserted++;
  }

  // Change runs with 3 lines of context, merged when the gap is <= 6 keeps.
  const hunks = [];
  let i = 0;
  while (i < total) {
    if (kinds[i] === 0) {
      i++;
      continue;
    }
    const runStart = i;
    while (i < total && kinds[i] !== 0) i++;
    const runEnd = i;
    const start = runStart - 3 < 0 ? 0 : runStart - 3;
    const end = runEnd + 3 > total ? total : runEnd + 3;
    const last = hunks[hunks.length - 1];
    if (last !== undefined && start <= last.end) {
      last.end = end;
    } else {
      hunks.push({ start, end });
    }
  }

  const out = [];
  out.push(`makefun-diff/1 old=${N} new=${M} hunks=${hunks.length} deleted=${deleted} inserted=${inserted}\n`);
  for (const h of hunks) {
    let oldBefore = 0;
    let newBefore = 0;
    for (let t = 0; t < h.start; t++) {
      if (kinds[t] !== 2) oldBefore++;
      if (kinds[t] !== 1) newBefore++;
    }
    let ol = 0;
    let nl = 0;
    for (let t = h.start; t < h.end; t++) {
      if (kinds[t] !== 2) ol++;
      if (kinds[t] !== 1) nl++;
    }
    out.push(`@ ${oldBefore + 1} ${ol} ${newBefore + 1} ${nl}\n`);
    let t = h.start;
    while (t < h.end) {
      if (kinds[t] === 0) {
        emitLine(out, '=', strs[a[ois[t]]]);
        t++;
      } else {
        // One change run: all deletions first, then all insertions.
        let u = t;
        while (u < h.end && kinds[u] !== 0) u++;
        for (let v = t; v < u; v++) if (kinds[v] === 1) emitLine(out, '-', strs[a[ois[v]]]);
        for (let v = t; v < u; v++) if (kinds[v] === 2) emitLine(out, '+', strs[b[nis[v]]]);
        t = u;
      }
    }
  }
  return out.join('');
}

function emitLine(out, mark, s) {
  if (s.charCodeAt(s.length - 1) === 10) out.push(mark + s);
  else out.push(mark + s + '\n%\n');
}
