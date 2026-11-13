// 手書きの判定（KanjiVG の書き順データと くらべる）
// 見るのは ①画数 ②書き順（1画ずつの 始点・向き・位置） ③おおまかな形。とめ・はね・はらいは 見ない。
// 座標は KanjiVG と同じ 0〜109 のマス。1画＝[[x,y],...]
(function () {
  const N = 24;            // 1画を何点に そろえるか
  const T = {              // 判定のしきい値（100×100 にそろえた座標での きょり）
    far: 22,               // 正しい画との ずれが これより大きい → 位置・形がちがう
    swap: 0.6,             // ほかの画のほうが これだけ近い → 書き順がちがう
    gap: 5,                // しかも これ以上 近い
    match: 18,             // 「ほかの画に近い」と言える きょり
    dirLen: 18,            // これより短い画（点など）は 向きを見ない
    dir: 0.55,             // 逆向きのほうが これだけ近い → 向きが逆
    shape: 8.5             // 字全体の形の ずれ（チャンファー距離）
  };

  function resample(pts, n) {
    if (pts.length < 2) return Array.from({ length: n }, () => pts[0].slice());
    const cum = [0];
    for (let i = 1; i < pts.length; i++) cum.push(cum[i - 1] + Math.hypot(pts[i][0] - pts[i - 1][0], pts[i][1] - pts[i - 1][1]));
    const L = cum[cum.length - 1];
    if (L < 1e-6) return Array.from({ length: n }, () => pts[0].slice());
    const out = []; let j = 1;
    for (let k = 0; k < n; k++) {
      const t = L * k / (n - 1);
      while (j < pts.length - 1 && cum[j] < t) j++;
      const a = pts[j - 1], b = pts[j], seg = cum[j] - cum[j - 1] || 1, r = Math.min(1, Math.max(0, (t - cum[j - 1]) / seg));
      out.push([a[0] + (b[0] - a[0]) * r, a[1] + (b[1] - a[1]) * r]);
    }
    return out;
  }
  const len = s => { let l = 0; for (let i = 1; i < s.length; i++) l += Math.hypot(s[i][0] - s[i - 1][0], s[i][1] - s[i - 1][1]); return l; };

  // 字全体を 100×100 に そろえる（大きさ・位置のちがいは 気にしない）
  function normalize(strokes) {
    let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity;
    strokes.forEach(s => s.forEach(([x, y]) => { x0 = Math.min(x0, x); y0 = Math.min(y0, y); x1 = Math.max(x1, x); y1 = Math.max(y1, y); }));
    const sc = 100 / Math.max(x1 - x0, y1 - y0, 1), cx = (x0 + x1) / 2, cy = (y0 + y1) / 2;
    return strokes.map(s => s.map(([x, y]) => [(x - cx) * sc + 50, (y - cy) * sc + 50]));
  }
  const cost = (a, b) => { let d = 0; for (let i = 0; i < a.length; i++) d += Math.hypot(a[i][0] - b[i][0], a[i][1] - b[i][1]); return d / a.length; };
  function chamfer(A, B) {
    const nn = (P, Q) => {
      let sum = 0;
      for (let i = 0; i < P.length; i++) {
        let m = Infinity; const px = P[i][0], py = P[i][1];
        for (let j = 0; j < Q.length; j++) { const dx = px - Q[j][0], dy = py - Q[j][1], d = dx * dx + dy * dy; if (d < m) m = d; }
        sum += Math.sqrt(m);
      }
      return sum / P.length;
    };
    return (nn(A, B) + nn(B, A)) / 2;
  }

  // ハンガリー法（いちばん合う 1対1の組み合わせ）。C は n×n
  function hungarian(C) {
    const n = C.length, INF = 1e18, u = Array(n + 1).fill(0), v = Array(n + 1).fill(0), p = Array(n + 1).fill(0), way = Array(n + 1).fill(0);
    for (let i = 1; i <= n; i++) {
      p[0] = i; let j0 = 0; const minv = Array(n + 1).fill(INF), used = Array(n + 1).fill(false);
      do {
        used[j0] = true; const i0 = p[j0]; let delta = INF, j1 = 0;
        for (let j = 1; j <= n; j++) if (!used[j]) {
          const cur = C[i0 - 1][j - 1] - u[i0] - v[j];
          if (cur < minv[j]) { minv[j] = cur; way[j] = j0; }
          if (minv[j] < delta) { delta = minv[j]; j1 = j; }
        }
        for (let j = 0; j <= n; j++) { if (used[j]) { u[p[j]] += delta; v[j] -= delta; } else minv[j] -= delta; }
        j0 = j1;
      } while (p[j0] !== 0);
      do { const j1 = way[j0]; p[j0] = p[j1]; j0 = j1; } while (j0);
    }
    const ans = Array(n);
    for (let j = 1; j <= n; j++) ans[p[j] - 1] = j - 1;
    return ans;
  }

  // お手本の画（SVGのパス → 点の列）。ブラウザの SVG で 長さにそって点を取る
  const cache = {};
  let host = null;
  function refRaw(c) {
    if (cache[c]) return cache[c];
    const ds = (window.STROKES || {})[c];
    if (!ds) return null;
    if (!host) {
      host = document.createElementNS("http://www.w3.org/2000/svg", "svg");
      host.setAttribute("width", "0"); host.setAttribute("height", "0");
      host.style.position = "absolute"; host.style.left = "-9999px";
      document.body.appendChild(host);
    }
    cache[c] = ds.map(d => {
      const p = document.createElementNS("http://www.w3.org/2000/svg", "path");
      p.setAttribute("d", d); host.appendChild(p);
      const L = p.getTotalLength(), pts = [];
      for (let k = 0; k <= 48; k++) { const q = p.getPointAtLength(L * k / 48); pts.push([q.x, q.y]); }
      host.removeChild(p);
      return pts;
    });
    return cache[c];
  }

  function judgeChar(c, user) {
    const raw = refRaw(c);
    if (!raw || !user || !user.length) return null;
    const ref = normalize(raw.map(s => resample(s, N)));
    const usr = normalize(user.map(s => resample(s, N)));
    // ③ 形：画の分け方に関係なく、線の重なり具合で見る
    const shapeScore = chamfer([].concat(...usr), [].concat(...ref));
    const res = {
      char: c,
      count: { ok: usr.length === ref.length, user: usr.length, ref: ref.length },
      order: { ok: false, checked: false, bad: [] },
      shape: { ok: shapeScore <= T.shape, score: +shapeScore.toFixed(1) }
    };
    // ② 書き順：画数が合っているときだけ、1画ずつ見る
    if (res.count.ok) {
      res.order.checked = true;
      // 書いた画 ↔ お手本の画 を、全体で いちばん合う組み合わせで 対応づける（向きは問わない）
      const C = usr.map(u => ref.map(r => Math.min(cost(u, r), cost(u.slice().reverse(), r))));
      const pi = hungarian(C);
      usr.forEach((u, i) => {
        const f = cost(u, ref[i]), rv = cost(u.slice().reverse(), ref[i]), j = pi[i];
        if (j !== i && C[i][j] < C[i][i] * T.swap && C[i][i] - C[i][j] > T.gap && C[i][j] < T.match) res.order.bad.push({ i, kind: "order", j });
        else if (len(ref[i]) > T.dirLen && rv < f * T.dir) res.order.bad.push({ i, kind: "dir" });
        else if (Math.min(f, rv) > T.far) res.order.bad.push({ i, kind: "far" });
      });
      res.order.ok = res.order.bad.length === 0;
    }
    res.ok = res.count.ok && res.order.ok && res.shape.ok;
    return res;
  }

  window.TEGAKI = { judgeChar, refRaw, resample, normalize, T };
})();
