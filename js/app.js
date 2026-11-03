// SVG Editor: canvas, tools, pen input, reference image and clipboard wiring.
// Stroke geometry lives in geometry.js (Geo), SVG import/export in svgio.js (Svgx).
(function () {
    'use strict';

    const SVG_NS = Svgx.SVG_NS;
    const STORE_KEY = 'svg-editor:doc';
    const REF_KEY = 'svg-editor:ref';
    const ERASE_RADIUS = 8; // screen px
    const SHAPE_KEYS = new Set(['count', 'density', 'n', 'mode', 'smooth', 'stab']);
    const FILL_KEYS = new Set(['fill', 'filled']);
    const SNAP_PX = 12; // a stroke starting or ending this close to another stroke's end joins it
    const TEXT_INPUTS = new Set(['text', 'number', 'search', 'email', 'url', 'password', 'tel']);

    const $ = (id) => document.getElementById(id);
    const clamp = (v, lo, hi) => Math.min(hi, Math.max(lo, v));
    const round = (v, k = 100) => Math.round(v * k) / k;

    const stage = $('stage');
    const viewportEl = $('viewport');
    const pageEl = $('page');
    const refEl = $('ref');
    const content = $('content');
    const liveEl = $('live');
    const overlay = $('overlay');
    const cursorLayer = $('cursorLayer');
    const snapLayer = $('snapLayer');

    const state = {
        tool: 'brush',
        view: { x: 0, y: 0, s: 1 },
        doc: { w: 1200, h: 800, bg: '#ffffff', exportBg: false, keepData: false },
        // pressure off = one centerline path with a stroke, which is what Figma edits as a single line
        // count 'length' = density anchors per 100 px of stroke; 'fixed' = n anchors whatever the length
        // fill only shows on closed shapes; connect joins strokes that meet at their ends
        brush: { color: '#1f1f24', width: 6, opacity: 1, pressure: false, minw: 0.15, gamma: 1, count: 'length', density: 5, n: 20, mode: 'shape', smooth: 1, stab: 4, filled: false, fill: '#b8c4ff', connect: true },
        ref: { src: '', name: '', nw: 0, nh: 0, x: 0, y: 0, w: 0, h: 0, opacity: 0.5, visible: true },
        anchors: 'auto', // 'auto' = selected strokes + the one just drawn
        sel: new Set(),
        lastStroke: null, // stays re-shapeable by the smoothing controls until anything else changes
        lastStrokeAt: -1,
        penSeen: false,
        space: false,
        pointer: null,
    };

    const rawCache = new WeakMap();
    const buildCache = new WeakMap(); // el → last Geo.build result (anchors, length)
    const touches = new Map();
    let gesture = null;

    // ---------- Elements and strokes ----------

    const drawables = () => Array.from(content.children).filter((el) => !Svgx.NON_GRAPHIC.has(el.localName));
    const ordered = () => drawables().filter((el) => state.sel.has(el));
    const isStroke = (el) => el.hasAttribute('data-raw') && el.hasAttribute('data-stroke');
    const selectedStrokes = () => ordered().filter(isStroke);
    const lookup = (id) => content.querySelector(`[id="${CSS.escape(id)}"]`);
    const dist = (a, b) => Math.hypot(b[0] - a[0], b[1] - a[1]);

    // data-raw holds one raw point list per joined stroke ("parts").

    function rawOf(el) {
        let raw = rawCache.get(el);
        if (!raw) {
            raw = Geo.decode(el.getAttribute('data-raw') || '');
            rawCache.set(el, raw);
        }
        return raw;
    }

    function cfgOf(el) {
        let saved = {};
        try { saved = JSON.parse(el.getAttribute('data-stroke')) || {}; } catch { /* fall back to brush settings */ }
        // Strokes saved before per-length counts existed used a fixed count; older strokes are open and unfilled.
        return { ...state.brush, step: 1, count: 'fixed', filled: false, closed: false, ...saved };
    }

    function buildOf(el) {
        let out = buildCache.get(el);
        if (!out) {
            out = Geo.build(rawOf(el), cfgOf(el));
            buildCache.set(el, out);
        }
        return out;
    }

    const anchorsOf = (el) => buildOf(el).anchors;

    function setParts(el, parts) {
        el.setAttribute('data-raw', Geo.encode(parts));
        rawCache.delete(el);
    }

    function paint(el, cfg) {
        if (cfg.pressure) {
            el.setAttribute('fill', cfg.color);
            ['stroke', 'stroke-width', 'stroke-linecap', 'stroke-linejoin'].forEach((a) => el.removeAttribute(a));
        } else {
            el.setAttribute('fill', cfg.closed && cfg.filled ? cfg.fill : 'none');
            el.setAttribute('stroke', cfg.color);
            el.setAttribute('stroke-width', Geo.fmt(cfg.width));
            el.setAttribute('stroke-linecap', 'round');
            el.setAttribute('stroke-linejoin', 'round');
        }
        if (cfg.opacity < 1) el.setAttribute('opacity', Geo.fmt(cfg.opacity));
        else el.removeAttribute('opacity');
    }

    function renderStroke(el, cfg) {
        const out = Geo.build(rawOf(el), cfg);
        el.setAttribute('d', out.d);
        paint(el, cfg);
        el.setAttribute('data-stroke', JSON.stringify(cfg));
        buildCache.set(el, out);
    }

    function docBBox(el, pad = isStroke(el) && !cfgOf(el).pressure ? cfgOf(el).width / 2 : 0) {
        let b;
        try { b = el.getBBox(); } catch { return null; }
        const m = Svgx.matrixOf(el);
        const xs = [], ys = [];
        for (const [x, y] of [[b.x - pad, b.y - pad], [b.x + b.width + pad, b.y - pad], [b.x - pad, b.y + b.height + pad], [b.x + b.width + pad, b.y + b.height + pad]]) {
            const q = m.transformPoint(new DOMPoint(x, y));
            xs.push(q.x);
            ys.push(q.y);
        }
        const x = Math.min(...xs), y = Math.min(...ys);
        return { x, y, w: Math.max(...xs) - x, h: Math.max(...ys) - y };
    }

    function unionBox(boxes) {
        if (!boxes.length) return null;
        const x = Math.min(...boxes.map((b) => b.x)), y = Math.min(...boxes.map((b) => b.y));
        return { x, y, w: Math.max(...boxes.map((b) => b.x + b.w)) - x, h: Math.max(...boxes.map((b) => b.y + b.h)) - y };
    }

    // Bounds including stroke width, so exported lines (pasted Figma paths too) aren't clipped at the edges.
    function paintedBox(el) {
        let width = 0;
        for (const n of [el, ...el.querySelectorAll('*')]) {
            if (n.closest('defs, clipPath, mask, pattern, symbol, marker')) continue;
            const cs = getComputedStyle(n);
            if (cs.stroke && cs.stroke !== 'none') width = Math.max(width, parseFloat(cs.strokeWidth) || 0);
        }
        return docBBox(el, width / 2);
    }

    // The exported SVG is cropped to what's drawn, rounded outward so nothing gets shaved off.
    function contentBox(items) {
        const u = unionBox(items.map(paintedBox).filter(Boolean));
        if (!u) return null;
        const x = Math.floor(u.x * 100) / 100, y = Math.floor(u.y * 100) / 100;
        return { x, y, w: Math.ceil((u.x + u.w) * 100) / 100 - x, h: Math.ceil((u.y + u.h) * 100) / 100 - y };
    }

    const rectFrom = (a, b) => ({ x: Math.min(a[0], b[0]), y: Math.min(a[1], b[1]), w: Math.abs(a[0] - b[0]), h: Math.abs(a[1] - b[1]) });
    const intersects = (a, b) => a.x <= b.x + b.w && a.x + a.w >= b.x && a.y <= b.y + b.h && a.y + a.h >= b.y;
    const translated = (el, dx, dy) => new DOMMatrix().translate(dx, dy).multiply(Svgx.matrixOf(el));

    // ---------- View ----------

    const stageRect = () => stage.getBoundingClientRect();
    const local = (e, r = stageRect()) => [e.clientX - r.left, e.clientY - r.top];
    const toDoc = ([sx, sy]) => [(sx - state.view.x) / state.view.s, (sy - state.view.y) / state.view.s];
    const toScreen = (x, y) => [x * state.view.s + state.view.x, y * state.view.s + state.view.y];

    function applyView() {
        const v = state.view;
        viewportEl.setAttribute('transform', `translate(${v.x} ${v.y}) scale(${v.s})`);
        $('zoomLabel').textContent = Math.round(v.s * 100) + '%';
        requestOverlay();
    }

    function zoomAt(factor, sx, sy) {
        const v = state.view;
        const s = clamp(v.s * factor, 0.02, 64);
        const k = s / v.s;
        v.x = sx - (sx - v.x) * k;
        v.y = sy - (sy - v.y) * k;
        v.s = s;
        applyView();
    }

    function zoomBy(factor) {
        const r = stageRect();
        zoomAt(factor, r.width / 2, r.height / 2);
    }

    function fitView() {
        const r = stageRect(), pad = 48;
        const s = clamp(Math.min((r.width - pad * 2) / state.doc.w, (r.height - pad * 2) / state.doc.h), 0.02, 8);
        state.view = { s, x: (r.width - state.doc.w * s) / 2, y: (r.height - state.doc.h * s) / 2 };
        applyView();
    }

    function viewCenterDoc() {
        const r = stageRect();
        return toDoc([r.width / 2, r.height / 2]);
    }

    function applyDoc() {
        const d = state.doc;
        pageEl.setAttribute('width', d.w);
        pageEl.setAttribute('height', d.h);
        pageEl.setAttribute('fill', d.bg);
        $('docW').value = d.w;
        $('docH').value = d.h;
        $('docBg').value = d.bg;
        $('exportBg').checked = d.exportBg;
        $('keepData').checked = d.keepData;
        updateStatus();
    }

    // ---------- Reference image ----------

    function applyRef() {
        const r = state.ref, has = !!r.src;
        if (has) {
            refEl.setAttribute('href', r.src);
            refEl.setAttribute('x', r.x);
            refEl.setAttribute('y', r.y);
            refEl.setAttribute('width', r.w);
            refEl.setAttribute('height', r.h);
            refEl.setAttribute('opacity', r.opacity);
        } else {
            refEl.removeAttribute('href');
        }
        refEl.style.display = has && r.visible ? '' : 'none';
        $('refInfo').textContent = has ? `${r.name} · ${r.nw} × ${r.nh} px` : 'None yet. Load, paste (Ctrl+V) or drop an image to trace over.';
        ['refRemove', 'refFitCanvas', 'refFitImage'].forEach((id) => { $(id).disabled = !has; });
        $('refOpacityRange').value = $('refOpacityNum').value = Math.round(r.opacity * 100);
        $('refVisible').checked = r.visible;
        updateEmpty();
    }

    let refWarned = false;
    function saveRef() {
        try {
            if (state.ref.src) localStorage.setItem(REF_KEY, JSON.stringify(state.ref));
            else localStorage.removeItem(REF_KEY);
        } catch {
            if (!refWarned) {
                refWarned = true;
                toast('This reference image is too big to remember after a reload. It stays for this session.');
            }
        }
    }

    function canvasToRef() {
        const r = state.ref;
        Object.assign(state.doc, { w: r.nw, h: r.nh });
        Object.assign(r, { x: 0, y: 0, w: r.nw, h: r.nh });
        applyDoc();
        applyRef();
        fitView();
        scheduleSave();
        saveRef();
    }

    function fitRefToCanvas() {
        const r = state.ref, s = Math.min(state.doc.w / r.nw, state.doc.h / r.nh);
        Object.assign(r, { w: r.nw * s, h: r.nh * s, x: (state.doc.w - r.nw * s) / 2, y: (state.doc.h - r.nh * s) / 2 });
        applyRef();
        saveRef();
    }

    function setRefSource(src, name) {
        const img = new Image();
        img.onload = () => {
            const replaced = !!state.ref.src;
            Object.assign(state.ref, { src, name, nw: img.naturalWidth, nh: img.naturalHeight, visible: true });
            // An empty canvas takes the image's size; otherwise the image fits the existing canvas.
            if (!drawables().length) canvasToRef();
            else fitRefToCanvas();
            toast(replaced ? 'Reference image replaced.' : 'Reference image set. It stays out of exports.');
        };
        img.onerror = () => toast('That image could not be read.');
        img.src = src;
    }

    function loadRefFile(file) {
        const reader = new FileReader();
        reader.onload = () => setRefSource(reader.result, file.name && file.name !== 'image.png' ? file.name : 'Pasted image');
        reader.readAsDataURL(file);
    }

    // ---------- History and persistence ----------

    const hist = { stack: [], index: -1 };

    function commit() {
        const snap = content.innerHTML;
        if (hist.stack[hist.index] === snap) return;
        hist.stack.splice(hist.index + 1);
        hist.stack.push(snap);
        let total = hist.stack.reduce((n, s) => n + s.length, 0);
        while (hist.stack.length > 1 && (hist.stack.length > 200 || total > 40e6)) total -= hist.stack.shift().length;
        hist.index = hist.stack.length - 1;
        endsCache = null;
        afterContentChange();
    }

    function restore(i) {
        hist.index = i;
        content.innerHTML = hist.stack[i];
        endsCache = null;
        state.lastStroke = null;
        state.sel.clear();
        selectionChanged();
        afterContentChange();
    }

    const undo = () => { if (hist.index > 0) restore(hist.index - 1); };
    const redo = () => { if (hist.index < hist.stack.length - 1) restore(hist.index + 1); };

    function afterContentChange() {
        $('btnUndo').disabled = hist.index <= 0;
        $('btnRedo').disabled = hist.index >= hist.stack.length - 1;
        updateEmpty();
        scheduleSave();
    }

    function updateEmpty() {
        stage.classList.toggle('is-empty', !content.firstElementChild && !state.ref.src);
    }

    let saveTimer = 0, saveWarned = false;
    function scheduleSave() {
        clearTimeout(saveTimer);
        saveTimer = setTimeout(save, 400);
    }

    function save() {
        try {
            localStorage.setItem(STORE_KEY, JSON.stringify({ v: 2, doc: state.doc, brush: state.brush, anchors: state.anchors, content: content.innerHTML }));
        } catch {
            if (!saveWarned) {
                saveWarned = true;
                toast('Autosave stopped: the drawing is bigger than browser storage allows. Export to keep it.', 6000);
            }
        }
    }

    function load() {
        try {
            const data = JSON.parse(localStorage.getItem(STORE_KEY) || 'null');
            if (data && (data.v === 1 || data.v === 2)) {
                Object.assign(state.doc, data.doc);
                Object.assign(state.brush, data.brush);
                if (data.v === 1) state.brush.pressure = false; // v1 defaulted to filled-outline strokes
                if (data.anchors) state.anchors = data.anchors;
                Svgx.fragment(data.content || '').forEach((n) => content.appendChild(n));
                // Strokes saved while a stale cached geometry.js was loaded have no usable points; drop them.
                content.querySelectorAll('[data-raw]').forEach((el) => { if (!Geo.decode(el.getAttribute('data-raw')).length) el.remove(); });
            }
        } catch { /* unreadable autosave: start fresh */ }
        try {
            const ref = JSON.parse(localStorage.getItem(REF_KEY) || 'null');
            if (ref && ref.src) Object.assign(state.ref, ref);
        } catch { /* no saved reference */ }
    }

    // ---------- Selection and properties panel ----------

    function setSelection(list) {
        state.sel = new Set(list);
        selectionChanged();
    }

    function selectionChanged() {
        syncControls();
        requestOverlay();
        updateStatus();
    }

    function lastStrokeLive() {
        const el = state.lastStroke;
        return !!el && el.isConnected && state.sel.size === 0 && hist.index === state.lastStrokeAt;
    }

    function panelCfg() {
        const strokes = selectedStrokes();
        return strokes.length ? cfgOf(strokes[0]) : state.brush;
    }

    // Edits go to the selected strokes if there are any, otherwise to the brush. Shape and fill settings
    // also apply to the stroke just drawn, so you can draw first and dial in the point count or fill after.
    function setParam(key, value, final, skip) {
        const patch = key === 'fill' ? { fill: value, filled: true } : { [key]: value }; // picking a fill colour turns fill on
        const strokes = selectedStrokes();
        if (strokes.length) {
            strokes.forEach((el) => renderStroke(el, { ...cfgOf(el), ...patch }));
            if (final) commit();
        } else {
            Object.assign(state.brush, patch);
            if ((SHAPE_KEYS.has(key) || FILL_KEYS.has(key)) && lastStrokeLive()) {
                const el = state.lastStroke;
                renderStroke(el, { ...cfgOf(el), ...patch });
                if (final) {
                    commit();
                    state.lastStrokeAt = hist.index;
                }
            }
            scheduleSave();
        }
        syncControls(skip);
        requestOverlay();
    }

    const CONTROLS = [
        { key: 'color', id: 'stroke', kind: 'color' },
        { key: 'filled', id: 'filled', kind: 'check' },
        { key: 'fill', id: 'fill', kind: 'color' },
        { key: 'width', id: 'width', kind: 'num', min: 0.5, max: 200, dp: 1 },
        { key: 'opacity', id: 'opacity', kind: 'num', min: 0, max: 100, scale: 100 },
        { key: 'pressure', id: 'pressure', kind: 'check' },
        { key: 'minw', id: 'minw', kind: 'num', min: 0, max: 100, scale: 100 },
        { key: 'gamma', id: 'gamma', kind: 'num', min: 0.2, max: 3, dp: 2 },
        { key: 'count', id: 'count', kind: 'radio' },
        { key: 'density', id: 'density', kind: 'num', min: 0.5, max: 200, dp: 1 },
        { key: 'n', id: 'points', kind: 'num', min: 2, max: 999 },
        { key: 'mode', id: 'mode', kind: 'radio' },
        { key: 'smooth', id: 'smooth', kind: 'num', min: 0, max: 100, scale: 100 },
        { key: 'stab', id: 'stab', kind: 'num', min: 0, max: 40 },
    ];

    function bindControls() {
        for (const c of CONTROLS) {
            if (c.kind === 'num') {
                const k = Math.pow(10, c.dp || 0);
                const read = (input) => {
                    const v = parseFloat(input.value);
                    if (!Number.isFinite(v)) return null;
                    const shown = Math.round(clamp(v, c.min, c.max) * k) / k;
                    return c.scale ? shown / c.scale : shown;
                };
                for (const input of [$(c.id + 'Range'), $(c.id + 'Num')]) {
                    input.addEventListener('input', () => {
                        const v = read(input);
                        if (v !== null) setParam(c.key, v, false, input);
                    });
                    input.addEventListener('change', () => {
                        const v = read(input);
                        if (v !== null) setParam(c.key, v, true);
                        else syncControls();
                    });
                }
            } else if (c.kind === 'color') {
                const picker = $(c.id + 'Color'), hex = $(c.id + 'Hex');
                picker.addEventListener('input', () => setParam(c.key, picker.value, false, picker));
                picker.addEventListener('change', () => setParam(c.key, picker.value, true));
                hex.addEventListener('change', () => {
                    const m = /^#?([0-9a-f]{6}|[0-9a-f]{3})$/i.exec(hex.value.trim());
                    if (!m) return syncControls();
                    const h = m[1].length === 3 ? m[1].replace(/./g, (ch) => ch + ch) : m[1];
                    setParam(c.key, '#' + h.toLowerCase(), true);
                });
            } else if (c.kind === 'check') {
                const box = $(c.id);
                box.addEventListener('change', () => setParam(c.key, box.checked, true));
            } else if (c.kind === 'radio') {
                document.querySelectorAll(`input[name="${c.id}"]`).forEach((r) => {
                    r.addEventListener('change', () => { if (r.checked) setParam(c.key, r.value, true); });
                });
            }
        }
    }

    function syncControls(skip) {
        const strokes = selectedStrokes();
        const cfg = panelCfg();
        for (const c of CONTROLS) {
            const v = cfg[c.key];
            if (c.kind === 'num') {
                const k = Math.pow(10, c.dp || 0);
                const shown = c.scale ? Math.round(v * c.scale) : Math.round(v * k) / k;
                for (const input of [$(c.id + 'Range'), $(c.id + 'Num')]) if (input !== skip) input.value = shown;
            } else if (c.kind === 'color') {
                if ($(c.id + 'Color') !== skip) $(c.id + 'Color').value = v;
                $(c.id + 'Hex').value = v;
            } else if (c.kind === 'check') {
                $(c.id).checked = !!v;
            } else if (c.kind === 'radio') {
                document.querySelectorAll(`input[name="${c.id}"]`).forEach((r) => { r.checked = r.value === v; });
            }
        }
        $('pressureOpts').classList.toggle('is-off', !cfg.pressure);
        $('fillRow').classList.toggle('is-off', !cfg.filled);
        $('connect').checked = !!state.brush.connect;
        const joinable = strokes.filter((el) => canJoin(el) && !cfgOf(el).closed);
        $('btnJoin').disabled = !joinable.length;
        $('btnJoin').textContent = joinable.length === 1 ? 'Close shape' : 'Join strokes';
        const note = cfg.pressure ? ''
            : cfg.filled && strokes.some((el) => !cfgOf(el).closed) ? 'Open strokes show no fill. Join or close them with Ctrl+J.'
            : cfg.filled && !strokes.length ? 'Shapes fill once a stroke closes them.' : '';
        $('fillNote').textContent = note;
        $('fillNote').hidden = !note;
        $('densityRow').hidden = cfg.count === 'fixed';
        $('pointsRow').hidden = cfg.count !== 'fixed';
        $('strokeTitle').textContent = strokes.length > 1 ? `${strokes.length} selected strokes` : strokes.length ? 'Selected stroke' : 'Brush';

        const readout = $('readout');
        const target = strokes[0] || (lastStrokeLive() ? state.lastStroke : null);
        if (!target) {
            readout.textContent = 'Draw a stroke to see how many anchors it gets.';
            return;
        }
        const info = buildOf(target), anchors = info.anchors.length, parts = rawOf(target);
        readout.innerHTML = `${strokes.length ? 'Selected' : 'Last stroke'}: <strong>${Math.round(info.length)} px</strong> long, ${parts.reduce((n, p) => n + p.length, 0)} input samples → <strong>${anchors}</strong> anchors`
            + (parts.length > 1 ? `, ${parts.length} strokes joined` : '') + (info.closed ? ', closed' : '')
            + (cfgOf(target).pressure ? ` <span>(filled outline, ${anchors * 2 + 2} nodes)</span>` : '')
            + (strokes.length ? '' : '. Points, spacing, curve and stabilize re-shape it until you draw again.');
    }

    // ---------- Overlay: selection, handles, anchors ----------

    let overlayQueued = false;
    function requestOverlay() {
        if (overlayQueued) return;
        overlayQueued = true;
        requestAnimationFrame(renderOverlay);
    }

    function renderOverlay() {
        overlayQueued = false;
        const px = (n) => Math.round(n) + 0.5;
        const rect = (b, cls) => {
            const [x0, y0] = toScreen(b.x, b.y), [x1, y1] = toScreen(b.x + b.w, b.y + b.h);
            return `<rect class="${cls}" x="${px(x0)}" y="${px(y0)}" width="${Math.max(0, Math.round(x1 - x0))}" height="${Math.max(0, Math.round(y1 - y0))}"/>`;
        };
        let out = '';
        const items = ordered();
        const boxes = items.map(docBBox).filter(Boolean);
        if (boxes.length > 1) boxes.forEach((b) => { out += rect(b, 'ov-item'); });
        const u = unionBox(boxes);
        if (u) out += rect(u, 'ov-box');

        const targets = new Set();
        if (state.anchors === 'all') content.querySelectorAll(':scope > [data-raw]').forEach((el) => targets.add(el));
        if (state.anchors !== 'off') {
            items.filter(isStroke).forEach((el) => targets.add(el));
            if (lastStrokeLive()) targets.add(state.lastStroke);
        }
        let mids = '', ends = '';
        for (const el of targets) {
            const m = Svgx.matrixOf(el), a = anchorsOf(el), open = !buildOf(el).closed;
            a.forEach((p, i) => {
                const q = m.transformPoint(new DOMPoint(p[0], p[1]));
                const [sx, sy] = toScreen(q.x, q.y);
                const end = open && (i === 0 || i === a.length - 1), r = end ? 3.5 : 2.75;
                const dot = `M${(sx - r).toFixed(1)},${sy.toFixed(1)}a${r},${r} 0 1,0 ${2 * r},0a${r},${r} 0 1,0 ${-2 * r},0Z`;
                if (end) ends += dot;
                else mids += dot;
            });
        }
        if (mids) out += `<path class="ov-anchor" d="${mids}"/>`;
        if (ends) out += `<path class="ov-end" d="${ends}"/>`;

        if (u && state.tool === 'select') {
            for (const [h, x, y] of [['nw', u.x, u.y], ['ne', u.x + u.w, u.y], ['sw', u.x, u.y + u.h], ['se', u.x + u.w, u.y + u.h]]) {
                const [sx, sy] = toScreen(x, y);
                out += `<rect class="ov-hit" data-handle="${h}" x="${sx - 11}" y="${sy - 11}" width="22" height="22"/>`;
                out += `<rect class="ov-handle" data-handle="${h}" x="${px(sx - 4)}" y="${px(sy - 4)}" width="8" height="8"/>`;
            }
        }
        if (gesture && gesture.type === 'marquee') out += rect(rectFrom(gesture.start, gesture.end), 'ov-marquee');
        overlay.innerHTML = out;
        renderSnap();
    }

    // Rings on the stroke ends a stroke will join: under the pointer while hovering, then at both ends while drawing.
    let snapQueued = false;
    function requestSnap() {
        if (snapQueued) return;
        snapQueued = true;
        requestAnimationFrame(renderSnap);
    }

    function renderSnap() {
        snapQueued = false;
        const g = gesture;
        let pts = [];
        if (g && g.type === 'stroke') {
            const s = snapsFor(g.raw, g.len, g.cfg);
            pts = [s.head, s.tail, s.loop && { x: g.raw[0][0], y: g.raw[0][1] }];
        } else if (!g && state.tool === 'brush' && state.pointer && !state.space && state.brush.connect && !state.brush.pressure) {
            pts = [nearestEnd(state.pointer[0], state.pointer[1], snapRadius(state.brush.width))];
        }
        snapLayer.innerHTML = pts.filter(Boolean).map((p) => {
            const [sx, sy] = toScreen(p.x, p.y), c = `cx="${sx.toFixed(1)}" cy="${sy.toFixed(1)}" r="7"`;
            return `<circle class="ov-snap-halo" ${c}/><circle class="ov-snap" ${c}/>`;
        }).join('');
    }

    function updateCursor(e) {
        const busy = gesture && (gesture.type === 'pan' || gesture.type === 'pinch');
        const erasing = state.tool === 'eraser' || (gesture && gesture.type === 'erase') || (e.pointerType === 'pen' && (e.buttons & 32));
        if ((state.tool !== 'brush' && !erasing) || state.space || busy || e.pointerType === 'touch') return hideCursor();
        const [sx, sy] = local(e);
        const r = erasing ? ERASE_RADIUS : Math.max(1.5, (panelCfg().width / 2) * state.view.s);
        for (const c of cursorLayer.children) {
            c.setAttribute('cx', sx);
            c.setAttribute('cy', sy);
            c.setAttribute('r', r);
        }
        cursorLayer.style.display = '';
    }

    function hideCursor() {
        cursorLayer.style.display = 'none';
    }

    // ---------- Input device badge ----------

    function noteInput(e) {
        const type = e.pointerType || 'mouse';
        const eraser = type === 'pen' && (e.button === 5 || (e.buttons & 32) !== 0);
        if (type === 'pen' && !state.penSeen) {
            state.penSeen = true;
            toast('Pen detected. One-finger touch now pans instead of drawing.', 4500);
        }
        $('inputBadge').dataset.type = type;
        $('inputLabel').textContent = type === 'pen' ? (eraser ? 'Pen eraser' : 'Pen') : type === 'touch' ? 'Touch' : 'Mouse';
        const p = type === 'pen' ? clamp(e.pressure || 0, 0, 1) : 0;
        $('pressureFill').style.transform = `scaleX(${p})`;
        $('pressureValue').textContent = type === 'pen' ? p.toFixed(2) : '—';
    }

    // ---------- Hit testing ----------

    const RING = (() => {
        const pts = [[0, 0]];
        for (const f of [0.5, 1]) {
            for (let i = 0; i < 8; i++) pts.push([Math.cos((i / 4) * Math.PI) * f, Math.sin((i / 4) * Math.PI) * f]);
        }
        return pts;
    })();

    function topLevel(node) {
        while (node && node !== content) {
            if (node.parentNode === content) return Svgx.NON_GRAPHIC.has(node.localName) ? null : node;
            node = node.parentNode;
        }
        return null;
    }

    // Thin strokes are hard to hit, so probe a small ring around the pointer too.
    function hitsAt(cx, cy, radius, firstOnly) {
        const found = [];
        for (const [ox, oy] of radius ? RING : [[0, 0]]) {
            for (const node of document.elementsFromPoint(cx + ox * radius, cy + oy * radius)) {
                const top = topLevel(node);
                if (top && !found.includes(top)) {
                    found.push(top);
                    if (firstOnly) return found;
                }
            }
        }
        return found;
    }

    const coalesced = (e) => {
        const list = typeof e.getCoalescedEvents === 'function' ? e.getCoalescedEvents() : [];
        return list.length ? list : [e];
    };

    // ---------- Gestures ----------

    function onPointerDown(e) {
        noteInput(e);
        stage.focus({ preventScroll: true });
        if (e.pointerType === 'touch') {
            touches.set(e.pointerId, local(e));
            if (touches.size === 2) {
                abortGesture();
                beginPinch();
                return;
            }
            if (touches.size > 2) return;
        }
        if (gesture || (e.pointerType === 'mouse' && e.button === 2)) return;
        e.preventDefault();
        try { stage.setPointerCapture(e.pointerId); } catch { /* pointer already gone */ }

        const penEraser = e.pointerType === 'pen' && (e.button === 5 || (e.buttons & 32));
        const pan = e.button === 1 || state.space || state.tool === 'hand'
            || (e.pointerType === 'pen' && (e.buttons & 2))         // barrel button
            || (e.pointerType === 'touch' && state.penSeen);         // palm rejection: fingers pan once a pen is in use
        if (penEraser) beginErase(e);
        else if (pan) beginPan(e);
        else if (state.tool === 'brush') beginStroke(e);
        else if (state.tool === 'eraser') beginErase(e);
        else if (state.tool === 'select') beginSelect(e);
    }

    function onPointerMove(e) {
        noteInput(e);
        if (touches.has(e.pointerId)) touches.set(e.pointerId, local(e));
        updateCursor(e);
        state.pointer = toDoc(local(e));
        updateStatus();
        if (state.tool === 'brush' || (gesture && gesture.type === 'stroke')) requestSnap();
        const g = gesture;
        if (!g) return;
        if (g.type === 'pinch') {
            if (touches.has(e.pointerId)) movePinch();
            return;
        }
        if (e.pointerId !== g.id) return;
        if (g.type === 'stroke') { addSamples(e); scheduleLive(); }
        else if (g.type === 'erase') eraseAt(e);
        else if (g.type === 'pan') movePan(e);
        else if (g.type === 'move') moveSelection(e);
        else if (g.type === 'scale') scaleSelection(e);
        else if (g.type === 'marquee') moveMarquee(e);
    }

    function onPointerUp(e) {
        touches.delete(e.pointerId);
        const g = gesture;
        if (!g) return;
        if (g.type === 'pinch') {
            if (touches.size < 2) gesture = null;
            return;
        }
        if (e.pointerId !== g.id) return;
        gesture = null;
        stage.classList.remove('is-panning');
        if (g.type === 'stroke') finishStroke(g);
        else if (g.type === 'erase') { if (g.removed) { commit(); selectionChanged(); } }
        else if ((g.type === 'move' || g.type === 'scale') && (g.moved || g.dup)) commit();
        requestOverlay();
    }

    function abortGesture() {
        const g = gesture;
        gesture = null;
        if (!g) return;
        if (g.type === 'stroke') liveEl.removeAttribute('d');
        if (g.type === 'move' || g.type === 'scale') {
            g.items.forEach((it) => Svgx.setMatrix(it.el, it.m));
            if (g.dup) commit();
        }
        if (g.type === 'erase' && g.removed) commit();
        stage.classList.remove('is-panning');
        requestOverlay();
    }

    // Stroke

    function beginStroke(e) {
        if (state.sel.size) setSelection([]);
        const cfg = { ...state.brush, step: round(clamp(1 / state.view.s, 0.02, 20), 1e4) };
        gesture = { type: 'stroke', id: e.pointerId, pointerType: e.pointerType, raw: [], len: 0, cfg, minGap: 0.35 / state.view.s };
        state.lastStroke = null;
        paint(liveEl, cfg);
        addSamples(e);
        scheduleLive();
    }

    function addSamples(e) {
        const g = gesture, r = stageRect();
        for (const ev of coalesced(e)) {
            const [x, y] = toDoc(local(ev, r));
            const p = g.pointerType === 'pen' ? clamp(ev.pressure || 0, 0, 1) : 1;
            const last = g.raw[g.raw.length - 1];
            const gap = last ? Math.hypot(x - last[0], y - last[1]) : 0;
            if (last && gap < g.minGap) {
                last[2] = p;
                continue;
            }
            g.raw.push([x, y, p]);
            g.len += gap;
        }
    }

    let liveQueued = false;
    function scheduleLive() {
        if (liveQueued) return;
        liveQueued = true;
        requestAnimationFrame(() => {
            liveQueued = false;
            if (gesture && gesture.type === 'stroke') liveEl.setAttribute('d', Geo.preview(gesture.raw, gesture.cfg));
        });
    }

    function finishStroke(g) {
        liveEl.removeAttribute('d');
        if (!g.raw.length) return;
        let el = joinNewStroke(g);
        if (!el) {
            el = document.createElementNS(SVG_NS, 'path');
            setParts(el, [g.raw]);
            content.appendChild(el);
            renderStroke(el, g.cfg);
        }
        state.lastStroke = el;
        commit();
        state.lastStrokeAt = hist.index;
        syncControls();
        requestSnap();
        const cfg = cfgOf(el);
        if (cfg.closed && !cfg.filled && !fillHinted) {
            fillHinted = true;
            toast('Closed shape. Tick Fill in the panel to fill it.', 4500);
        }
    }

    // Joining strokes

    const snapRadius = (width) => Math.max(SNAP_PX / state.view.s, width / 2);
    const canJoin = (el) => isStroke(el) && !cfgOf(el).pressure;
    const firstPt = (parts) => parts[0][0];
    const lastPt = (parts) => parts[parts.length - 1][parts[parts.length - 1].length - 1];
    const sameEnd = (a, b) => !!a && !!b && a.el === b.el && a.atStart === b.atStart;
    const mapParts = (parts, m) => parts.map((part) => part.map(([x, y, pr]) => {
        const q = m.transformPoint(new DOMPoint(x, y));
        return [q.x, q.y, pr];
    }));
    let fillHinted = false;

    // Open ends of the top-level strokes in document coordinates. Ends only move on commits, which clear this.
    let endsCache = null;
    function openEnds() {
        if (endsCache) return endsCache;
        endsCache = [];
        for (const el of content.children) {
            if (!canJoin(el) || cfgOf(el).closed) continue;
            const parts = rawOf(el);
            if (!parts.length) continue;
            const m = Svgx.matrixOf(el);
            for (const [p, atStart] of [[firstPt(parts), true], [lastPt(parts), false]]) {
                const q = m.transformPoint(new DOMPoint(p[0], p[1]));
                endsCache.push({ el, atStart, x: q.x, y: q.y });
            }
        }
        return endsCache;
    }

    function nearestEnd(x, y, r, not) {
        let best = null, bd = r;
        for (const e of openEnds()) {
            const d = Math.hypot(e.x - x, e.y - y);
            if (d <= bd && !sameEnd(e, not)) { best = e; bd = d; }
        }
        return best;
    }

    // What a stroke in progress connects to: head/tail are open ends of strokes it starts/ends on,
    // loop means it ends back on its own start.
    function snapsFor(raw, len, cfg) {
        const r = snapRadius(cfg.width), out = { head: null, tail: null, loop: false, r };
        if (!state.brush.connect || cfg.pressure || !raw.length) return out;
        const first = raw[0], last = raw[raw.length - 1];
        out.head = nearestEnd(first[0], first[1], r);
        if (len < r) return out; // still a tap: only the start counts so far
        out.tail = nearestEnd(last[0], last[1], r, out.head);
        out.loop = !out.head && !out.tail && len >= 4 * r && dist(first, last) <= r;
        return out;
    }

    // The new stroke becomes another part of the stroke it starts on (or ends on), starting exactly at that
    // stroke's end with a corner, no smoothing across the join. Ending on a second stroke merges that one in
    // too; ending back on the same stroke closes the shape.
    function joinNewStroke(g) {
        const s = snapsFor(g.raw, g.len, g.cfg);
        if (g.len < s.r || !(s.head || s.tail || s.loop)) return null;
        if (s.loop) {
            const el = document.createElementNS(SVG_NS, 'path');
            setParts(el, [Geo.pinEnd(g.raw, g.raw[0], false)]);
            content.appendChild(el);
            renderStroke(el, { ...g.cfg, closed: true });
            return el;
        }
        const target = (s.head || s.tail).el;
        const inv = Svgx.matrixOf(target).inverse();
        let part = mapParts([g.raw], inv)[0];
        let parts = [];
        if (s.head) {
            const a = rawOf(target);
            parts = s.head.atStart ? Geo.reverse(a) : a;
            part = Geo.pinEnd(part, lastPt(parts), true);
        }
        let closed = false, after = [];
        if (s.tail && s.head && s.tail.el === target) {
            closed = true;
            part = Geo.pinEnd(part, firstPt(parts), false);
        } else if (s.tail) {
            const c = s.tail.el === target ? rawOf(target) : mapParts(rawOf(s.tail.el), inv.multiply(Svgx.matrixOf(s.tail.el)));
            after = s.tail.atStart ? c : Geo.reverse(c);
            part = Geo.pinEnd(part, firstPt(after), false);
            if (s.tail.el !== target) s.tail.el.remove();
        }
        const cfg = cfgOf(target);
        setParts(target, [...parts, part, ...after]);
        renderStroke(target, { ...cfg, closed, ...(cfg.filled ? {} : { filled: g.cfg.filled, fill: g.cfg.fill }) });
        return target;
    }

    // Ctrl+J: chain the selected strokes into one path, nearest ends first. Gaps within snapping distance
    // close up; wider ones get a straight line. A single open stroke gets closed.
    function joinSelection() {
        const strokes = selectedStrokes().filter((el) => canJoin(el) && !cfgOf(el).closed);
        if (!strokes.length) {
            return toast(state.sel.size ? 'Only open strokes with pressure off can be joined.' : 'Select strokes to join, or one stroke to close.');
        }
        const target = strokes[0], r = snapRadius(cfgOf(target).width);
        const pool = strokes.map((el) => mapParts(rawOf(el), Svgx.matrixOf(el))); // document coordinates
        let chain = pool.shift();
        while (pool.length) {
            const cs = firstPt(chain), ce = lastPt(chain);
            let best = null;
            pool.forEach((parts, i) => {
                const ps = firstPt(parts), pe = lastPt(parts);
                for (const [d, append, flip] of [[dist(ce, ps), true, false], [dist(ce, pe), true, true], [dist(cs, pe), false, false], [dist(cs, ps), false, true]]) {
                    if (!best || d < best.d) best = { i, d, append, flip };
                }
            });
            let parts = pool.splice(best.i, 1)[0];
            if (best.flip) parts = Geo.reverse(parts);
            if (best.d <= r) parts = pinParts(parts, best.append ? ce : cs, best.append);
            chain = best.append ? [...chain, ...parts] : [...parts, ...chain];
        }
        const gap = dist(firstPt(chain), lastPt(chain));
        const closed = strokes.length === 1 || gap <= r;
        if (closed && gap <= r) chain = pinParts(chain, firstPt(chain), false);
        strokes.slice(1).forEach((el) => el.remove());
        setParts(target, mapParts(chain, Svgx.matrixOf(target).inverse()));
        renderStroke(target, { ...cfgOf(target), closed });
        setTool('select');
        setSelection([target]);
        commit();
        const what = strokes.length === 1 ? 'Closed the stroke' : `Joined ${strokes.length} strokes${closed ? ' into a closed shape' : ''}`;
        toast(what + (closed && !cfgOf(target).filled ? '. Tick Fill to fill it.' : '.'));
    }

    // Pin the start of the first part, or the end of the last part, onto p.
    function pinParts(parts, p, atStart) {
        const out = parts.slice(), i = atStart ? 0 : out.length - 1;
        out[i] = Geo.pinEnd(out[i], p, atStart);
        return out;
    }

    // Eraser

    function beginErase(e) {
        gesture = { type: 'erase', id: e.pointerId, removed: 0 };
        eraseAt(e);
    }

    function eraseAt(e) {
        for (const ev of coalesced(e)) {
            for (const el of hitsAt(ev.clientX, ev.clientY, ERASE_RADIUS, false)) {
                el.remove();
                state.sel.delete(el);
                gesture.removed++;
            }
        }
    }

    // Pan and pinch

    function beginPan(e) {
        const [sx, sy] = local(e);
        gesture = { type: 'pan', id: e.pointerId, sx, sy, vx: state.view.x, vy: state.view.y };
        stage.classList.add('is-panning');
        hideCursor();
    }

    function movePan(e) {
        const g = gesture, [sx, sy] = local(e);
        state.view.x = g.vx + sx - g.sx;
        state.view.y = g.vy + sy - g.sy;
        applyView();
    }

    function pinchInfo() {
        const [a, b] = Array.from(touches.values());
        return { d: Math.hypot(b[0] - a[0], b[1] - a[1]) || 1, mx: (a[0] + b[0]) / 2, my: (a[1] + b[1]) / 2 };
    }

    function beginPinch() {
        gesture = { type: 'pinch', ...pinchInfo() };
        hideCursor();
    }

    function movePinch() {
        const g = gesture, now = pinchInfo();
        state.view.x += now.mx - g.mx;
        state.view.y += now.my - g.my;
        zoomAt(now.d / g.d, now.mx, now.my);
        Object.assign(g, now);
    }

    // Select, move, scale, marquee

    function beginSelect(e) {
        const p = toDoc(local(e));
        const handle = e.target.closest && e.target.closest('[data-handle]');
        if (handle && state.sel.size) return beginScale(e, handle.getAttribute('data-handle'));
        const hit = hitsAt(e.clientX, e.clientY, 5, true)[0];
        if (!hit) {
            gesture = { type: 'marquee', id: e.pointerId, start: p, end: p, base: e.shiftKey ? new Set(state.sel) : new Set() };
            if (!e.shiftKey) setSelection([]);
            return;
        }
        if (e.shiftKey && state.sel.has(hit)) {
            state.sel.delete(hit);
            return selectionChanged();
        }
        if (e.shiftKey) {
            state.sel.add(hit);
            selectionChanged();
        } else if (!state.sel.has(hit)) {
            setSelection([hit]);
        }
        let items = ordered();
        if (e.altKey) {
            items = cloneElements(items);
            setSelection(items);
        }
        gesture = { type: 'move', id: e.pointerId, start: p, items: items.map((el) => ({ el, m: Svgx.matrixOf(el) })), moved: false, dup: e.altKey };
    }

    function moveSelection(e) {
        const g = gesture, p = toDoc(local(e));
        let dx = p[0] - g.start[0], dy = p[1] - g.start[1];
        if (e.shiftKey) {
            if (Math.abs(dx) > Math.abs(dy)) dy = 0;
            else dx = 0;
        }
        if (!g.moved && Math.hypot(dx, dy) * state.view.s < 2) return; // a click shouldn't count as a move
        g.moved = true;
        for (const it of g.items) Svgx.setMatrix(it.el, new DOMMatrix().translate(dx, dy).multiply(it.m));
        requestOverlay();
    }

    function beginScale(e, corner) {
        const items = ordered();
        const box = unionBox(items.map(docBBox).filter(Boolean));
        if (!box) return;
        gesture = {
            type: 'scale',
            id: e.pointerId,
            ax: corner.includes('w') ? box.x + box.w : box.x, // fixed opposite corner
            ay: corner.includes('n') ? box.y + box.h : box.y,
            cx: corner.includes('w') ? box.x : box.x + box.w, // grabbed corner
            cy: corner.includes('n') ? box.y : box.y + box.h,
            items: items.map((el) => ({ el, m: Svgx.matrixOf(el) })),
            moved: false,
        };
    }

    function scaleSelection(e) {
        const g = gesture, [x, y] = toDoc(local(e));
        let sx = Math.abs(g.cx - g.ax) > 1e-6 ? (x - g.ax) / (g.cx - g.ax) : 1;
        let sy = Math.abs(g.cy - g.ay) > 1e-6 ? (y - g.ay) / (g.cy - g.ay) : 1;
        if (e.shiftKey) {
            const s = Math.max(Math.abs(sx), Math.abs(sy));
            sx = Math.sign(sx || 1) * s;
            sy = Math.sign(sy || 1) * s;
        }
        sx = Math.sign(sx || 1) * Math.max(0.01, Math.abs(sx));
        sy = Math.sign(sy || 1) * Math.max(0.01, Math.abs(sy));
        const M = new DOMMatrix().translate(g.ax, g.ay).scale(sx, sy).translate(-g.ax, -g.ay);
        for (const it of g.items) Svgx.setMatrix(it.el, M.multiply(it.m));
        g.moved = true;
        requestOverlay();
    }

    function moveMarquee(e) {
        const g = gesture;
        g.end = toDoc(local(e));
        const r = rectFrom(g.start, g.end);
        const hits = drawables().filter((el) => {
            const b = docBBox(el);
            return b && intersects(b, r);
        });
        state.sel = new Set([...g.base, ...hits]);
        selectionChanged();
    }

    // ---------- Commands ----------

    function cloneElements(items) {
        return items.map((el) => {
            const c = el.cloneNode(true);
            content.appendChild(c);
            Svgx.uniquifyIds(c);
            return c;
        });
    }

    function duplicateSelection() {
        const items = ordered();
        if (!items.length) return;
        const clones = cloneElements(items);
        clones.forEach((c) => Svgx.setMatrix(c, translated(c, 10, 10)));
        setSelection(clones);
        commit();
    }

    function deleteSelection() {
        const items = ordered();
        if (!items.length) return;
        items.forEach((el) => el.remove());
        setSelection([]);
        commit();
    }

    function nudge(dx, dy) {
        const items = ordered();
        if (!items.length) return false;
        items.forEach((el) => Svgx.setMatrix(el, translated(el, dx, dy)));
        commit();
        requestOverlay();
        return true;
    }

    function restack(dir) {
        const items = ordered();
        if (!items.length) return;
        for (const el of dir > 0 ? items.slice().reverse() : items) {
            let sib = dir > 0 ? el.nextElementSibling : el.previousElementSibling;
            while (sib && Svgx.NON_GRAPHIC.has(sib.localName)) sib = dir > 0 ? sib.nextElementSibling : sib.previousElementSibling;
            if (!sib || state.sel.has(sib)) continue;
            if (dir > 0) sib.after(el);
            else sib.before(el);
        }
        commit();
        requestOverlay();
    }

    function groupSelection() {
        const items = ordered();
        if (items.length < 2) return;
        const g = document.createElementNS(SVG_NS, 'g');
        items[items.length - 1].after(g);
        items.forEach((el) => g.appendChild(el));
        setSelection([g]);
        commit();
    }

    const CLIPPING = ['clip-path', 'mask', 'filter'];

    function ungroupSelection() {
        const out = [];
        let changed = false;
        for (const g of ordered()) {
            if (g.localName !== 'g') {
                out.push(g);
                continue;
            }
            changed = true;
            const gm = Svgx.matrixOf(g);
            const clipped = CLIPPING.some((a) => g.hasAttribute(a));
            for (const child of Array.from(g.children)) {
                if (Svgx.NON_GRAPHIC.has(child.localName)) {
                    g.before(child);
                    continue;
                }
                let el = child;
                if (clipped && child.hasAttribute('transform')) {
                    // The clip is in the group's coordinates; keep a wrapper so it still lines up.
                    el = g.cloneNode(false);
                    el.removeAttribute('id');
                    el.appendChild(child);
                } else {
                    const m = gm.multiply(Svgx.matrixOf(child));
                    Svgx.inherit(Array.from(g.attributes), child);
                    Svgx.setMatrix(child, m);
                }
                g.before(el);
                out.push(el);
            }
            g.remove();
        }
        if (!changed) return;
        setSelection(out);
        commit();
    }

    // A pasted SVG arrives wrapped in a group; a lone shape doesn't need the wrapper.
    function unwrapSingle(g) {
        const kids = Array.from(g.children);
        if (kids.length !== 1 || Svgx.NON_GRAPHIC.has(kids[0].localName)) return g;
        const child = kids[0];
        if (CLIPPING.some((a) => g.hasAttribute(a)) && child.hasAttribute('transform')) return g;
        const m = Svgx.matrixOf(g).multiply(Svgx.matrixOf(child));
        Svgx.inherit(Array.from(g.attributes), child);
        g.replaceWith(child);
        Svgx.setMatrix(child, m);
        return child;
    }

    function newDrawing() {
        if (!content.firstElementChild) return;
        content.textContent = '';
        state.lastStroke = null;
        setSelection([]);
        commit();
        toast('Canvas cleared. Ctrl+Z brings the drawing back.');
    }

    function exportSVG() {
        const items = drawables();
        return Svgx.serialize(items, contentBox(items) || { x: 0, y: 0, w: state.doc.w, h: state.doc.h }, {
            lookup,
            keepData: state.doc.keepData,
            background: state.doc.exportBg ? state.doc.bg : null,
        });
    }

    function exportFile() {
        const url = URL.createObjectURL(new Blob([exportSVG()], { type: 'image/svg+xml' }));
        const a = document.createElement('a');
        a.href = url;
        a.download = 'drawing.svg';
        document.body.appendChild(a);
        a.click();
        a.remove();
        setTimeout(() => URL.revokeObjectURL(url), 1000);
    }

    function openSVG(text, name) {
        const res = Svgx.prepare(text);
        if (!res) return toast(`${name} isn't an SVG this editor can read.`);
        content.textContent = '';
        for (const n of res.nodes) {
            content.appendChild(n);
            if (Svgx.NON_GRAPHIC.has(n.localName)) continue;
            Svgx.inherit(res.attrs, n);
            Svgx.setMatrix(n, res.m.multiply(Svgx.matrixOf(n)));
        }
        if (res.w && res.h) Object.assign(state.doc, { w: Math.max(1, Math.round(res.w)), h: Math.max(1, Math.round(res.h)) });
        state.lastStroke = null;
        applyDoc();
        setSelection([]);
        commit();
        fitView();
        toast(`Opened ${name}.`);
    }

    // ---------- Clipboard ----------

    let internalClip = null; // last copy from this editor, kept with its editable stroke data
    let pasteCount = 0;
    let copyTimer = 0, pasteTimer = 0;
    let pasteInPlaceNext = false; // Ctrl+Shift+V

    function copySelection(cut) {
        const items = ordered();
        const text = Svgx.serialize(items, contentBox(items) || { x: 0, y: 0, w: 1, h: 1 }, { lookup });
        internalClip = { text, markup: items.map((el) => el.outerHTML).join('') };
        pasteCount = cut ? -1 : 0;
        toast(`${cut ? 'Cut' : 'Copied'} ${items.length === 1 ? '1 object' : items.length + ' objects'} as SVG. Ctrl+V in Figma pastes editable vectors.`);
        return text;
    }

    async function writeClipboard(text) {
        try {
            await navigator.clipboard.writeText(text);
            return true;
        } catch { /* fall back to a hidden textarea */ }
        const ta = document.createElement('textarea');
        ta.value = text;
        ta.style.cssText = 'position:fixed;opacity:0;pointer-events:none';
        document.body.appendChild(ta);
        ta.select();
        let ok = false;
        try { ok = document.execCommand('copy'); } catch { /* blocked */ }
        ta.remove();
        return ok;
    }

    async function copyButton() {
        const text = state.sel.size ? copySelection(false) : exportSVG();
        const ok = await writeClipboard(text);
        if (!ok) toast('The browser blocked clipboard access.');
        else if (!state.sel.size) toast('Copied the whole drawing as SVG.');
    }

    function handlePaste({ files, text, html }, inPlace) {
        text = (text || '').replace(/\r\n/g, '\n');
        html = html || '';
        const svgFile = files.find((f) => f.type === 'image/svg+xml');
        const image = files.find((f) => f.type.startsWith('image/') && f !== svgFile);
        if (internalClip && text && text === internalClip.text) return pasteInternal(inPlace);
        if (/<svg[\s>]/i.test(text)) return pasteSVG(text, inPlace);
        if (svgFile) return svgFile.text().then((t) => pasteSVG(t, inPlace));
        if (/<svg[\s>]/i.test(html)) return pasteSVG(html, inPlace);
        if (image) return loadRefFile(image);
        if (/figmeta|\(figma\)/i.test(html)) {
            return toast('That is Figma’s own clipboard format. In Figma, right-click → Copy/Paste as → Copy as SVG for vectors, or Copy as PNG for a reference image.', 8000);
        }
        toast('Nothing to paste: the clipboard has no SVG or image.');
    }

    function pasteSVG(text, inPlace) {
        const res = Svgx.prepare(text);
        if (!res || !res.nodes.length) return toast('That SVG could not be read.');
        const g = document.createElementNS(SVG_NS, 'g');
        res.attrs.forEach((a) => Svgx.copyAttr(g, a));
        res.nodes.forEach((n) => g.appendChild(n));
        content.appendChild(g);
        Svgx.setMatrix(g, res.m);
        const el = unwrapSingle(g);
        // Same size as the canvas (e.g. a Figma frame you sized it to) means it already lines up.
        const lineUp = inPlace || (Math.round(res.w) === state.doc.w && Math.round(res.h) === state.doc.h);
        if (!lineUp) {
            const b = docBBox(el);
            const [cx, cy] = viewCenterDoc();
            if (b) Svgx.setMatrix(el, translated(el, cx - b.x - b.w / 2, cy - b.y - b.h / 2));
        }
        setTool('select');
        setSelection([el]);
        commit();
        const shapes = el.localName === 'g'
            ? Array.from(el.querySelectorAll('path, rect, circle, ellipse, line, polyline, polygon, text, image, use')).filter((n) => !n.closest('defs, clipPath, mask, pattern, symbol')).length
            : 1;
        toast(`Pasted SVG: ${shapes} shape${shapes === 1 ? '' : 's'}${lineUp ? ', at its original position' : ''}.`);
    }

    function pasteInternal(inPlace) {
        const nodes = Svgx.fragment(internalClip.markup);
        pasteCount += 1;
        const d = inPlace ? 0 : Math.max(0, pasteCount) * 10; // repeated pastes step down-right instead of stacking
        nodes.forEach((n) => {
            content.appendChild(n);
            Svgx.uniquifyIds(n);
            if (d) Svgx.setMatrix(n, translated(n, d, d));
        });
        setTool('select');
        setSelection(nodes);
        commit();
    }

    // Clipboard through the async API, for buttons and for Safari, which can skip the paste event.
    // Null when the browser refuses. Images need the full read; plain text is the fallback for SVG code.
    async function readClipboard(needImage) {
        const clip = navigator.clipboard;
        if (clip && clip.read) {
            try {
                const data = { files: [], text: '', html: '' };
                for (const item of await clip.read()) {
                    for (const type of item.types) {
                        const blob = await item.getType(type);
                        if (type === 'text/plain') data.text = await blob.text();
                        else if (type === 'text/html') data.html = await blob.text();
                        else if (type.startsWith('image/')) data.files.push(new File([blob], 'Pasted image', { type }));
                    }
                }
                return data;
            } catch { /* denied or unsupported; try plain text */ }
        }
        if (!needImage && clip && clip.readText) {
            try { return { files: [], text: await clip.readText(), html: '' }; } catch { /* denied */ }
        }
        return null;
    }

    const CLIP_BLOCKED = 'The browser blocked clipboard access. Click the canvas and press Ctrl+V instead.';

    async function pasteFromApi(inPlace) {
        const data = await readClipboard(false);
        if (data) handlePaste(data, inPlace);
        else toast(CLIP_BLOCKED);
    }

    // Reference → Paste: takes the clipboard image even when SVG code sits beside it.
    async function pasteRef() {
        const data = await readClipboard(true);
        if (!data) return toast(CLIP_BLOCKED);
        const image = data.files.find((f) => f.type.startsWith('image/'));
        if (image) return loadRefFile(image);
        if (/figmeta|\(figma\)/i.test(data.html)) return toast('In Figma, use Copy as PNG (Shift+Ctrl+C), then paste here.', 7000);
        toast('No image on the clipboard. Copy an image or take a screenshot (Win+Shift+S) first.');
    }

    // ---------- Tools, status, toast ----------

    const HINTS = {
        brush: 'Draw · [ ] width · , . fewer / more points · Space-drag or the pen barrel button pans',
        select: 'Click or drag a box to select · Shift adds · Alt-drag duplicates · drag a corner to scale',
        eraser: 'Drag across strokes to delete them · the pen’s eraser end works in any tool',
        hand: 'Drag to pan · Ctrl+wheel or pinch to zoom',
    };

    function setTool(tool) {
        state.tool = tool;
        stage.dataset.tool = tool;
        document.querySelectorAll('.tool[data-tool]').forEach((b) => b.setAttribute('aria-pressed', String(b.dataset.tool === tool)));
        if (tool === 'brush' && state.sel.size) setSelection([]);
        $('hint').textContent = HINTS[tool];
        hideCursor();
        requestOverlay();
        requestSnap();
    }

    function updateStatus() {
        let s = `${state.doc.w} × ${state.doc.h}`;
        if (state.sel.size) s = `${state.sel.size} selected · ${s}`;
        if (state.pointer) s += ` · ${Math.round(state.pointer[0])}, ${Math.round(state.pointer[1])}`;
        $('status').textContent = s;
    }

    let toastTimer = 0;
    function toast(msg, ms = 3000) {
        const t = $('toast');
        t.textContent = msg;
        t.classList.add('is-on');
        clearTimeout(toastTimer);
        toastTimer = setTimeout(() => t.classList.remove('is-on'), ms);
    }

    // ---------- Wiring ----------

    const isTyping = (t) => !!t && (t.isContentEditable || t.tagName === 'TEXTAREA' || (t.tagName === 'INPUT' && TEXT_INPUTS.has(t.type)));

    function onKeyDown(e) {
        const t = e.target;
        if (isTyping(t)) {
            if (e.key === 'Escape') t.blur();
            return;
        }
        const onButton = t.tagName === 'BUTTON' || t.tagName === 'SUMMARY' || (t.tagName === 'INPUT' && (t.type === 'checkbox' || t.type === 'radio'));
        const onSlider = t.tagName === 'INPUT' && (t.type === 'range' || t.type === 'radio');
        const mod = e.ctrlKey || e.metaKey;
        const key = e.key.length === 1 ? e.key.toLowerCase() : e.key;

        if (key === ' ' && !onButton) {
            e.preventDefault();
            if (!state.space) {
                state.space = true;
                stage.classList.add('can-pan');
                hideCursor();
            }
            return;
        }
        if (mod) {
            switch (key) {
                case 'z': e.preventDefault(); return e.shiftKey ? redo() : undo();
                case 'y': e.preventDefault(); return redo();
                case 'a': e.preventDefault(); setTool('select'); return setSelection(drawables());
                case 'd': e.preventDefault(); return duplicateSelection();
                case 'g': e.preventDefault(); return e.shiftKey ? ungroupSelection() : groupSelection();
                case 'j': e.preventDefault(); return joinSelection();
                case 's': e.preventDefault(); return exportFile();
                case '=': case '+': e.preventDefault(); return zoomBy(1.25);
                case '-': case '_': e.preventDefault(); return zoomBy(0.8);
                case '0': e.preventDefault(); return fitView();
                case ']': e.preventDefault(); return restack(1);
                case '[': e.preventDefault(); return restack(-1);
                case 'c': case 'x':
                    // Safari skips the copy event when no text is selected; fall back to the async API.
                    if (state.sel.size) {
                        const cut = key === 'x';
                        copyTimer = setTimeout(() => {
                            writeClipboard(copySelection(cut));
                            if (cut) deleteSelection();
                        }, 0);
                    }
                    return;
                case 'v': {
                    const inPlace = e.shiftKey;
                    pasteTimer = setTimeout(() => pasteFromApi(inPlace), 150);
                    pasteInPlaceNext = inPlace;
                    return;
                }
            }
            return;
        }
        if (onSlider && key.startsWith('Arrow')) return;
        if (e.altKey) return;
        const step = e.shiftKey ? 10 : 1;
        switch (key) {
            case 'v': setTool('select'); break;
            case 'b': case 'p': setTool('brush'); break;
            case 'e': setTool('eraser'); break;
            case 'h': setTool('hand'); break;
            case 'Escape': setSelection([]); break;
            case 'Delete': case 'Backspace': e.preventDefault(); deleteSelection(); break;
            case '[': setParam('width', Math.max(0.5, round(panelCfg().width / 1.25, 10)), true); break;
            case ']': setParam('width', Math.min(200, round(panelCfg().width * 1.25, 10)), true); break;
            case ',': case '<': stepPoints(-1, e.shiftKey); break;
            case '.': case '>': stepPoints(1, e.shiftKey); break;
            case 'ArrowLeft': if (nudge(-step, 0)) e.preventDefault(); break;
            case 'ArrowRight': if (nudge(step, 0)) e.preventDefault(); break;
            case 'ArrowUp': if (nudge(0, -step)) e.preventDefault(); break;
            case 'ArrowDown': if (nudge(0, step)) e.preventDefault(); break;
            default:
                if (e.shiftKey && e.code === 'Digit1') fitView();
                else if (e.shiftKey && e.code === 'Digit0') zoomBy(1 / state.view.s);
        }
    }

    function stepPoints(dir, big) {
        const c = panelCfg(), by = dir * (big ? 5 : 1);
        if (c.count === 'fixed') setParam('n', clamp(c.n + by, 2, 999), true);
        else setParam('density', clamp(c.density + by, 0.5, 200), true);
    }

    function bindUi() {
        stage.addEventListener('pointerdown', onPointerDown);
        stage.addEventListener('pointermove', onPointerMove);
        stage.addEventListener('pointerup', onPointerUp);
        stage.addEventListener('pointercancel', onPointerUp);
        stage.addEventListener('pointerleave', () => {
            hideCursor();
            state.pointer = null;
            updateStatus();
            requestSnap();
        });
        stage.addEventListener('contextmenu', (e) => e.preventDefault());
        stage.addEventListener('wheel', (e) => {
            e.preventDefault();
            const [sx, sy] = local(e);
            const unit = e.deltaMode === 1 ? 16 : e.deltaMode === 2 ? stageRect().height : 1;
            const dx = e.deltaX * unit, dy = e.deltaY * unit;
            if (e.ctrlKey || e.metaKey) zoomAt(Math.exp(-clamp(dy, -40, 40) * 0.01), sx, sy);
            else if (e.shiftKey && !dx) { state.view.x -= dy; applyView(); }
            else { state.view.x -= dx; state.view.y -= dy; applyView(); }
        }, { passive: false });
        document.addEventListener('gesturestart', (e) => e.preventDefault()); // Safari page pinch-zoom

        document.addEventListener('keydown', onKeyDown);
        document.addEventListener('keyup', (e) => {
            if (e.key === ' ') {
                state.space = false;
                stage.classList.remove('can-pan');
            }
        });
        window.addEventListener('blur', () => {
            state.space = false;
            stage.classList.remove('can-pan');
        });
        // Mouse clicks shouldn't leave focus on buttons, or Space would press them instead of panning.
        document.addEventListener('click', (e) => {
            const b = e.target.closest('button');
            if (b && e.detail > 0) b.blur();
        });

        document.addEventListener('copy', (e) => {
            clearTimeout(copyTimer);
            if (isTyping(e.target) || !state.sel.size) return;
            e.preventDefault();
            e.clipboardData.setData('text/plain', copySelection(false));
        });
        document.addEventListener('cut', (e) => {
            clearTimeout(copyTimer);
            if (isTyping(e.target) || !state.sel.size) return;
            e.preventDefault();
            e.clipboardData.setData('text/plain', copySelection(true));
            deleteSelection();
        });
        document.addEventListener('paste', (e) => {
            clearTimeout(pasteTimer);
            const dt = e.clipboardData;
            const files = Array.from(dt.files || []);
            // A focused text box can't take an image, so an image still becomes the reference.
            if (isTyping(e.target) && !files.some((f) => f.type.startsWith('image/'))) return;
            e.preventDefault();
            handlePaste({ files, text: dt.getData('text/plain'), html: dt.getData('text/html') }, pasteInPlaceNext);
            pasteInPlaceNext = false;
        });

        window.addEventListener('dragover', (e) => e.preventDefault());
        window.addEventListener('drop', (e) => e.preventDefault());
        stage.addEventListener('dragover', (e) => {
            e.preventDefault();
            stage.classList.add('is-drop');
        });
        stage.addEventListener('dragleave', (e) => {
            if (!stage.contains(e.relatedTarget)) stage.classList.remove('is-drop');
        });
        stage.addEventListener('drop', (e) => {
            e.preventDefault();
            stage.classList.remove('is-drop');
            const files = Array.from(e.dataTransfer.files);
            const svg = files.find((f) => f.type === 'image/svg+xml' || /\.svg$/i.test(f.name));
            const img = files.find((f) => f.type.startsWith('image/') && f !== svg);
            if (svg) svg.text().then((t) => pasteSVG(t, false));
            else if (img) loadRefFile(img);
            else {
                const t = e.dataTransfer.getData('text/plain');
                if (/<svg[\s>]/i.test(t)) pasteSVG(t, false);
            }
        });

        document.querySelectorAll('.tool[data-tool]').forEach((b) => b.addEventListener('click', () => setTool(b.dataset.tool)));
        $('btnUndo').addEventListener('click', undo);
        $('btnRedo').addEventListener('click', redo);
        $('btnNew').addEventListener('click', newDrawing);
        $('btnOpen').addEventListener('click', () => $('fileOpen').click());
        $('btnExport').addEventListener('click', exportFile);
        $('btnCopy').addEventListener('click', copyButton);
        $('btnPaste').addEventListener('click', () => pasteFromApi(false));
        $('zoomIn').addEventListener('click', () => zoomBy(1.25));
        $('zoomOut').addEventListener('click', () => zoomBy(0.8));
        $('zoomLabel').addEventListener('click', fitView);
        $('panelToggle').addEventListener('click', () => {
            const open = document.body.classList.toggle('panel-open');
            $('panelToggle').setAttribute('aria-expanded', String(open));
        });

        $('fileOpen').addEventListener('change', async (e) => {
            const f = e.target.files[0];
            e.target.value = '';
            if (f) openSVG(await f.text(), f.name);
        });
        $('fileRef').addEventListener('change', (e) => {
            const f = e.target.files[0];
            e.target.value = '';
            if (f) loadRefFile(f);
        });

        $('btnJoin').addEventListener('click', joinSelection);
        $('connect').addEventListener('change', (e) => {
            state.brush.connect = e.target.checked;
            scheduleSave();
            requestSnap();
        });

        $('refLoad').addEventListener('click', () => $('fileRef').click());
        $('refPaste').addEventListener('click', pasteRef);
        $('refRemove').addEventListener('click', () => {
            state.ref.src = '';
            applyRef();
            saveRef();
        });
        for (const input of [$('refOpacityRange'), $('refOpacityNum')]) {
            input.addEventListener('input', () => {
                const v = parseFloat(input.value);
                if (!Number.isFinite(v)) return;
                state.ref.opacity = clamp(v, 0, 100) / 100;
                applyRef();
            });
            input.addEventListener('change', saveRef);
        }
        $('refVisible').addEventListener('change', (e) => {
            state.ref.visible = e.target.checked;
            applyRef();
            saveRef();
        });
        $('refFitCanvas').addEventListener('click', canvasToRef);
        $('refFitImage').addEventListener('click', fitRefToCanvas);

        for (const [id, key] of [['docW', 'w'], ['docH', 'h']]) {
            $(id).addEventListener('change', (e) => {
                const v = Math.round(parseFloat(e.target.value));
                if (Number.isFinite(v)) state.doc[key] = clamp(v, 1, 20000);
                applyDoc();
                scheduleSave();
            });
        }
        $('docBg').addEventListener('input', (e) => {
            state.doc.bg = e.target.value;
            applyDoc();
            scheduleSave();
        });
        $('exportBg').addEventListener('change', (e) => { state.doc.exportBg = e.target.checked; scheduleSave(); });
        $('keepData').addEventListener('change', (e) => { state.doc.keepData = e.target.checked; scheduleSave(); });
        document.querySelectorAll('input[name="anchors"]').forEach((r) => {
            r.checked = r.value === state.anchors;
            r.addEventListener('change', () => {
                if (!r.checked) return;
                state.anchors = r.value;
                requestOverlay();
                scheduleSave();
            });
        });

        window.addEventListener('resize', requestOverlay);
    }

    // ---------- Start ----------

    load();
    bindControls();
    bindUi();
    applyDoc();
    applyRef();
    setTool('brush');
    syncControls();
    hist.stack = [content.innerHTML];
    hist.index = 0;
    afterContentChange();
    hideCursor();
    fitView();
})();
