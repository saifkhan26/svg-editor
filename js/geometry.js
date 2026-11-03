// Stroke geometry: reduce raw pointer samples to N anchors and build smooth SVG path data.
// A point is [x, y, pressure].
(function (global) {
    'use strict';

    const EPS = 1e-6;
    const dist = (a, b) => Math.hypot(b[0] - a[0], b[1] - a[1]);
    const lerp = (a, b, t) => [a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, a[2] + (b[2] - a[2]) * t];

    function fmt(v) {
        const r = Math.round(v * 100) / 100;
        return Object.is(r, -0) ? '0' : String(r);
    }
    const pt = (p) => fmt(p[0]) + ',' + fmt(p[1]);

    function pathLength(pts) {
        let len = 0;
        for (let i = 1; i < pts.length; i++) len += dist(pts[i - 1], pts[i]);
        return len;
    }

    // Uniform spacing makes the stabilizer radius mean the same thing at any input rate.
    function resampleSpacing(pts, step) {
        if (pts.length < 2) return pts.slice();
        const out = [pts[0]];
        let carry = 0; // distance travelled since the last emitted sample
        for (let i = 1; i < pts.length; i++) {
            const a = pts[i - 1], b = pts[i], seg = dist(a, b);
            if (seg < EPS) continue;
            let t = step - carry;
            while (t <= seg) {
                out.push(lerp(a, b, t / seg));
                t += step;
            }
            carry = seg - (t - step);
        }
        const last = pts[pts.length - 1];
        if (dist(out[out.length - 1], last) > EPS) out.push(last);
        return out;
    }

    // Moving average whose window shrinks near the ends, so the stroke still starts and stops where the pen did.
    function stabilize(pts, radius) {
        const n = pts.length;
        radius = Math.round(radius);
        if (radius < 1 || n < 3) return pts.slice();
        const sx = new Float64Array(n + 1), sy = new Float64Array(n + 1), sp = new Float64Array(n + 1);
        for (let i = 0; i < n; i++) {
            sx[i + 1] = sx[i] + pts[i][0];
            sy[i + 1] = sy[i] + pts[i][1];
            sp[i + 1] = sp[i] + pts[i][2];
        }
        const out = new Array(n);
        for (let i = 0; i < n; i++) {
            const r = Math.min(radius, i, n - 1 - i);
            const a = i - r, b = i + r + 1, c = b - a;
            out[i] = [(sx[b] - sx[a]) / c, (sy[b] - sy[a]) / c, (sp[b] - sp[a]) / c];
        }
        return out;
    }

    // Exactly n points, endpoints included: keep adding the sample that strays furthest from the current polyline.
    // pw > 0 also counts pressure changes (in px of half-width) as error, so width swells keep an anchor.
    // Once every span is flatter than tol, spare points split the longest spans instead of bunching up.
    function simplifyToCount(pts, n, pw, tol) {
        const len = pts.length;
        if (len <= n) return pts.slice();
        const err = (i, a, b) => {
            const A = pts[a], B = pts[b], P = pts[i];
            const dx = B[0] - A[0], dy = B[1] - A[1], l2 = dx * dx + dy * dy;
            const t = l2 > EPS ? Math.max(0, Math.min(1, ((P[0] - A[0]) * dx + (P[1] - A[1]) * dy) / l2)) : 0;
            let e = Math.hypot(P[0] - A[0] - dx * t, P[1] - A[1] - dy * t);
            if (pw) e += Math.abs(P[2] - (A[2] + (B[2] - A[2]) * t)) * pw;
            return e;
        };
        const span = (a, b) => {
            let idx = -1, worst = -1;
            for (let i = a + 1; i < b; i++) {
                const e = err(i, a, b);
                if (e > worst) { worst = e; idx = i; }
            }
            if (idx >= 0 && worst < tol) {
                idx = (a + b) >> 1;
                worst = (tol * (b - a)) / len; // always below tol, so real bends still win
            }
            return { a, b, idx, worst };
        };
        const keep = new Uint8Array(len);
        keep[0] = keep[len - 1] = 1;
        const spans = [span(0, len - 1)];
        for (let count = 2; count < n; count++) {
            let best = -1;
            for (let i = 0; i < spans.length; i++) {
                if (spans[i].idx >= 0 && (best < 0 || spans[i].worst > spans[best].worst)) best = i;
            }
            if (best < 0) break;
            const s = spans[best];
            keep[s.idx] = 1;
            spans.splice(best, 1, span(s.a, s.idx), span(s.idx, s.b));
        }
        return pts.filter((_, i) => keep[i]);
    }

    // Exactly n points spread evenly by arc length.
    function resampleCount(pts, n) {
        if (pts.length < 2) return pts.slice();
        const cum = [0];
        for (let i = 1; i < pts.length; i++) cum.push(cum[i - 1] + dist(pts[i - 1], pts[i]));
        const total = cum[cum.length - 1];
        if (total < EPS) return [pts[0]];
        const out = [];
        let j = 0;
        for (let k = 0; k < n; k++) {
            const t = (total * k) / (n - 1);
            while (j < pts.length - 2 && cum[j + 1] < t) j++;
            const seg = cum[j + 1] - cum[j];
            out.push(lerp(pts[j], pts[j + 1], seg > EPS ? (t - cum[j]) / seg : 0));
        }
        return out;
    }

    // Centripetal Catmull-Rom (alpha 0.5, so no cusps or loops) for segment p1→p2, as cubic Bézier controls.
    // smooth 0..1 pulls the controls back onto the anchors (0 = straight lines).
    function controls(p0, p1, p2, p3, smooth) {
        const d1 = Math.sqrt(dist(p0, p1)), d2 = Math.sqrt(dist(p1, p2)), d3 = Math.sqrt(dist(p2, p3));
        let c1 = [p1[0], p1[1]], c2 = [p2[0], p2[1]];
        if (d1 > EPS) {
            const a = 2 * d1 * d1 + 3 * d1 * d2 + d2 * d2, m = 3 * d1 * (d1 + d2);
            c1 = [(p1[0] * a - p0[0] * d2 * d2 + p2[0] * d1 * d1) / m, (p1[1] * a - p0[1] * d2 * d2 + p2[1] * d1 * d1) / m];
        }
        if (d3 > EPS) {
            const b = 2 * d3 * d3 + 3 * d3 * d2 + d2 * d2, m = 3 * d3 * (d3 + d2);
            c2 = [(p2[0] * b + p1[0] * d3 * d3 - p3[0] * d2 * d2) / m, (p2[1] * b + p1[1] * d3 * d3 - p3[1] * d2 * d2) / m];
        }
        if (smooth < 1) {
            c1 = [p1[0] + (c1[0] - p1[0]) * smooth, p1[1] + (c1[1] - p1[1]) * smooth];
            c2 = [p2[0] + (c2[0] - p2[0]) * smooth, p2[1] + (c2[1] - p2[1]) * smooth];
        }
        return [c1, c2];
    }

    // Path commands after the initial M. Phantom end points are reflections, so the ends keep their direction.
    // A seamed loop (last point on the first) uses its neighbours across the seam instead, so it closes smoothly.
    function segments(pts, smooth, seam) {
        const n = pts.length;
        let d = '';
        if (smooth <= 0 || n < 3) {
            for (let i = 1; i < n; i++) d += ' L' + pt(pts[i]);
            return d;
        }
        const head = seam ? pts[n - 2] : [2 * pts[0][0] - pts[1][0], 2 * pts[0][1] - pts[1][1]];
        const tail = seam ? pts[1] : [2 * pts[n - 1][0] - pts[n - 2][0], 2 * pts[n - 1][1] - pts[n - 2][1]];
        for (let i = 0; i < n - 1; i++) {
            const [c1, c2] = controls(i > 0 ? pts[i - 1] : head, pts[i], pts[i + 1], i + 2 < n ? pts[i + 2] : tail, smooth);
            d += ' C' + pt(c1) + ' ' + pt(c2) + ' ' + pt(pts[i + 1]);
        }
        return d;
    }

    function centerline(pts, smooth) {
        if (pts.length < 2 || pathLength(pts) < 0.01) {
            const p = pts[0];
            return `M${pt(p)} L${fmt(p[0] + 0.01)},${fmt(p[1])}`; // zero-length lines lose their round caps
        }
        return 'M' + pt(pts[0]) + segments(pts, smooth);
    }

    function halfWidth(p, cfg) {
        const k = Math.pow(Math.max(0, Math.min(1, p)), cfg.gamma || 1);
        return Math.max(0.05, (cfg.width / 2) * (cfg.minw + (1 - cfg.minw) * k));
    }

    function circle(c, r) {
        return `M${fmt(c[0] - r)},${fmt(c[1])} a${fmt(r)},${fmt(r)} 0 1,0 ${fmt(2 * r)},0 a${fmt(r)},${fmt(r)} 0 1,0 ${fmt(-2 * r)},0 Z`;
    }

    // Filled outline for width-varying strokes: offset each anchor along its normal, spline both sides, round caps.
    function outline(pts, cfg, smooth) {
        const n = pts.length;
        const hw = pts.map((p) => halfWidth(p[2], cfg));
        if (n < 2 || pathLength(pts) < 0.01) return circle(pts[0], Math.max(...hw));
        const left = [], right = [];
        let nx = 0, ny = 1;
        for (let i = 0; i < n; i++) {
            const a = pts[Math.max(0, i - 1)], b = pts[Math.min(n - 1, i + 1)];
            const tx = b[0] - a[0], ty = b[1] - a[1], m = Math.hypot(tx, ty);
            if (m > EPS) { nx = -ty / m; ny = tx / m; }
            left.push([pts[i][0] + nx * hw[i], pts[i][1] + ny * hw[i]]);
            right.push([pts[i][0] - nx * hw[i], pts[i][1] - ny * hw[i]]);
        }
        right.reverse();
        const cap = (r, to) => ` A${fmt(r)},${fmt(r)} 0 0,0 ${pt(to)}`;
        return 'M' + pt(left[0]) + segments(left, smooth) + cap(hw[n - 1], right[0]) + segments(right, smooth) + cap(hw[0], left[0]) + ' Z';
    }

    function prepare(raw, cfg) {
        return stabilize(resampleSpacing(raw, cfg.step || 1), cfg.stab || 0);
    }

    // parts: raw point lists drawn end to end as one path (joined strokes). Each part gets its own anchors,
    // so joining never re-shapes a stroke; a part that starts away from the previous end gets a straight line.
    // cfg: { count: 'length'|'fixed', density (anchors per 100 units), n, mode: 'shape'|'even',
    //        smooth 0..1, stab, step, pressure, width, minw, gamma, closed }
    function build(parts, cfg) {
        parts = parts.filter((p) => p.length);
        if (!parts.length) return { anchors: [], d: '', length: 0, closed: false };
        const closed = !!cfg.closed && !cfg.pressure;
        const loop = closed && parts.length === 1; // one stroke drawn round to its own start
        let length = 0;
        const runs = parts.map((raw) => {
            const pts = prepare(raw, cfg);
            const len = pathLength(pts);
            length += len;
            const n = Math.max(loop ? 4 : 2, clampCount(cfg.count === 'length' ? (len * cfg.density) / 100 : cfg.n));
            return cfg.mode === 'even'
                ? resampleCount(pts, n)
                : simplifyToCount(pts, n, cfg.pressure ? cfg.width / 2 : 0, (cfg.step || 1) * 0.25);
        });
        const anchors = [];
        for (const run of runs) {
            const prev = anchors[anchors.length - 1];
            anchors.push(...(prev && dist(prev, run[0]) < 0.01 ? run.slice(1) : run));
        }
        if (closed && anchors.length > 1 && dist(anchors[0], anchors[anchors.length - 1]) < 0.01) anchors.pop();
        if (cfg.pressure) return { anchors, length, closed, d: runs.map((a) => outline(a, cfg, cfg.smooth)).join(' ') };

        let d = '';
        runs.forEach((a, i) => {
            if (i === 0) {
                const seam = loop && a.length > 3 && dist(a[0], a[a.length - 1]) < 0.01;
                d = seam ? 'M' + pt(a[0]) + segments(a, cfg.smooth, true) : centerline(a, cfg.smooth);
                return;
            }
            const end = runs[i - 1][runs[i - 1].length - 1];
            if (dist(end, a[0]) >= 0.01) d += ' L' + pt(a[0]);
            d += segments(a, cfg.smooth);
        });
        return { anchors, length, closed, d: closed ? d + ' Z' : d };
    }

    const clampCount = (n) => Math.min(999, Math.max(2, Math.round(n || 2)));

    const reverse = (parts) => parts.slice().reverse().map((p) => p.slice().reverse());

    // Start (or end) a raw part exactly on p by adding p as its first (last) sample. The pen samples
    // stay as drawn, so the join is a corner at p rather than a curve blended into the other stroke.
    function pinEnd(part, p, atStart) {
        const at = atStart ? part[0] : part[part.length - 1];
        if (dist(at, p) < EPS) return part;
        const q = [p[0], p[1], at[2]];
        return atStart ? [q, ...part] : [...part, q];
    }

    // Full-resolution path for the stroke in progress (no simplification, so it tracks the pen exactly).
    function preview(raw, cfg) {
        if (!raw.length) return '';
        const pts = prepare(raw, cfg);
        return cfg.pressure ? outline(pts, cfg, 0) : centerline(pts, 0);
    }

    // data-raw holds one "x,y,p x,y,p" list per joined stroke, separated by " | ".
    function encode(parts) {
        return parts.map((pts) => pts.map((p) => fmt(p[0]) + ',' + fmt(p[1]) + ',' + Math.round(p[2] * 1000) / 1000).join(' ')).join(' | ');
    }

    function decode(str) {
        return str.split('|').map((chunk) => {
            const out = [];
            for (const tok of chunk.trim().split(/\s+/)) {
                const [x, y, p] = tok.split(',').map(Number);
                if (Number.isFinite(x) && Number.isFinite(y)) out.push([x, y, Number.isFinite(p) ? p : 1]);
            }
            return out;
        }).filter((p) => p.length);
    }

    global.Geo = { build, preview, encode, decode, fmt, pathLength, reverse, pinEnd };
})(window);
