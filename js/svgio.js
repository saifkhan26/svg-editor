// SVG in and out: sanitize foreign markup (Figma "Copy as SVG", files), keep ids unique, serialize selections.
(function (global) {
    'use strict';

    const SVG_NS = 'http://www.w3.org/2000/svg';
    const BLOCKED = new Set(['script', 'foreignobject', 'iframe', 'object', 'embed', 'set', 'animate', 'animatemotion', 'animatetransform', 'handler', 'listener']);
    const ROOT_SKIP = new Set(['width', 'height', 'viewbox', 'x', 'y', 'version', 'preserveaspectratio', 'id', 'class', 'baseprofile', 'enable-background', 'xml:space']);
    const NON_GRAPHIC = new Set(['defs', 'style', 'title', 'desc', 'metadata']);
    const UNITS = { px: 1, pt: 4 / 3, pc: 16, mm: 96 / 25.4, cm: 96 / 2.54, in: 96, em: 16, rem: 16 };
    const SAFE_URL = /^(#|data:image\/)/i;

    const round = (v, k) => Math.round(v * k) / k;
    const tree = (root) => [root, ...root.querySelectorAll('*')];

    function matrixOf(el) {
        let m = new DOMMatrix();
        const list = el.transform && el.transform.baseVal;
        if (list) for (let i = 0; i < list.numberOfItems; i++) m = m.multiply(DOMMatrix.fromMatrix(list.getItem(i).matrix));
        return m;
    }

    function setMatrix(el, m) {
        const [a, b, c, d, e, f] = [m.a, m.b, m.c, m.d, m.e, m.f].map((v) => round(v, 1e4));
        if (a === 1 && b === 0 && c === 0 && d === 1) {
            if (e === 0 && f === 0) el.removeAttribute('transform');
            else el.setAttribute('transform', `translate(${round(e, 1e3)} ${round(f, 1e3)})`);
        } else {
            el.setAttribute('transform', `matrix(${a} ${b} ${c} ${d} ${e} ${f})`);
        }
    }

    // Attributes with an unbound prefix (e.g. "sketch:type" via the HTML parser) can't be set; skip them.
    function copyAttr(el, attr) {
        try { el.setAttributeNS(attr.namespaceURI, attr.name, attr.value); } catch { /* unbound prefix */ }
    }

    function parse(text) {
        const start = text.search(/<svg[\s>]/i);
        if (start < 0) return null;
        const end = text.toLowerCase().lastIndexOf('</svg>');
        const src = end > start ? text.slice(start, end + 6) : text.slice(start);
        const xml = new DOMParser().parseFromString(src, 'image/svg+xml');
        let root = xml.documentElement;
        if (!root || xml.getElementsByTagName('parsererror').length || root.namespaceURI !== SVG_NS) {
            // Missing xmlns or HTML-isms: the HTML parser is forgiving and still yields real SVG elements.
            root = new DOMParser().parseFromString(src, 'text/html').querySelector('svg');
        }
        return root && root.localName === 'svg' ? root : null;
    }

    // <style> rules would leak into the editor page, so fold them into style attributes instead.
    function inlineStyles(root) {
        for (const styleEl of Array.from(root.querySelectorAll('style'))) {
            try {
                const sheet = new CSSStyleSheet();
                sheet.replaceSync(styleEl.textContent);
                const rulesFor = new Map();
                for (const rule of sheet.cssRules) {
                    if (!(rule instanceof CSSStyleRule)) continue;
                    let targets;
                    try { targets = root.querySelectorAll(rule.selectorText); } catch { continue; }
                    for (const el of targets) {
                        if (!rulesFor.has(el)) rulesFor.set(el, []);
                        rulesFor.get(el).push(rule.style.cssText);
                    }
                }
                for (const [el, rules] of rulesFor) {
                    const own = el.getAttribute('style');
                    el.setAttribute('style', rules.concat(own ? [own] : []).join(';'));
                }
            } catch { /* unreadable stylesheet: dropping it is safer than leaking it */ }
            styleEl.remove();
        }
    }

    function sanitize(root) {
        for (const el of Array.from(root.querySelectorAll('*'))) {
            if (BLOCKED.has(el.localName.toLowerCase())) el.remove();
        }
        inlineStyles(root);
        for (const el of tree(root)) {
            for (const attr of Array.from(el.attributes)) {
                const name = attr.name.toLowerCase();
                const isUrl = name === 'href' || name.endsWith(':href') || name === 'src';
                const value = attr.value.replace(/[\s\u0000-\u001f]+/g, '');
                if (name.startsWith('on') || (isUrl && !SAFE_URL.test(value))) el.removeAttributeNode(attr);
            }
        }
    }

    let seq = 0;
    const salt = Math.random().toString(36).slice(2, 6);

    // Pasting the same Figma export twice would otherwise make both copies share gradients, clips and masks.
    function uniquifyIds(root) {
        const all = tree(root);
        const map = new Map();
        for (const el of all) {
            const id = el.getAttribute('id');
            if (!id) continue;
            const fresh = `${id}_${salt}${(seq++).toString(36)}`;
            map.set(id, fresh);
            el.setAttribute('id', fresh);
        }
        if (!map.size) return;
        const swap = (id) => map.get(id) || id;
        for (const el of all) {
            for (const attr of Array.from(el.attributes)) {
                let v = attr.value;
                if (/(^|:)href$/i.test(attr.name) && v.startsWith('#')) v = '#' + swap(v.slice(1));
                else if (v.includes('url(')) v = v.replace(/url\(\s*(['"]?)#([^'")]+)\1\s*\)/g, (_m, _q, id) => `url(#${swap(id.trim())})`);
                if (v !== attr.value) attr.value = v;
            }
        }
    }

    function parseLength(v) {
        const m = /^\s*([\d.]+(?:e[-+]?\d+)?)\s*([a-z]*)\s*$/i.exec(v || '');
        if (!m) return 0;
        const n = parseFloat(m[1]) * (UNITS[m[2].toLowerCase() || 'px'] || 1);
        return Number.isFinite(n) && n > 0 ? n : 0;
    }

    // Map the root's viewBox onto its width/height, the same way the browser would.
    function viewportOf(root) {
        const vb = (root.getAttribute('viewBox') || '').trim().split(/[\s,]+/).map(Number);
        let w = parseLength(root.getAttribute('width')), h = parseLength(root.getAttribute('height'));
        if (!(vb.length === 4 && vb.every(Number.isFinite) && vb[2] > 0 && vb[3] > 0)) return { m: new DOMMatrix(), w, h };
        if (!w && !h) { w = vb[2]; h = vb[3]; }
        else if (!w) w = (h * vb[2]) / vb[3];
        else if (!h) h = (w * vb[3]) / vb[2];
        const par = (root.getAttribute('preserveAspectRatio') || '').trim();
        let sx = w / vb[2], sy = h / vb[3], tx = 0, ty = 0;
        if (!par.startsWith('none')) {
            const s = /slice/.test(par) ? Math.max(sx, sy) : Math.min(sx, sy);
            tx = (w - vb[2] * s) / 2; // xMidYMid; other alignments are rare in pasted SVG
            ty = (h - vb[3] * s) / 2;
            sx = sy = s;
        }
        return { m: new DOMMatrix([sx, 0, 0, sy, tx - vb[0] * sx, ty - vb[1] * sy]), w, h };
    }

    // Parse foreign SVG text into sanitized nodes owned by this document.
    // Returns { nodes, attrs (root presentation attributes), m (viewBox matrix), w, h } or null.
    function prepare(text) {
        const root = parse(text);
        if (!root) return null;
        sanitize(root);
        uniquifyIds(root);
        const { m, w, h } = viewportOf(root);
        const attrs = Array.from(root.attributes).filter((a) => !ROOT_SKIP.has(a.name.toLowerCase()) && !a.name.startsWith('xmlns'));
        const nodes = Array.from(root.children).map((n) => document.importNode(n, true));
        return { nodes, attrs, m, w, h };
    }

    // Parse markup this editor produced earlier (autosave, internal clipboard) into inert, sanitized nodes.
    function fragment(markup) {
        const doc = new DOMParser().parseFromString(`<svg xmlns="${SVG_NS}">${markup}</svg>`, 'text/html');
        const root = doc.querySelector('svg');
        if (!root) return [];
        sanitize(root);
        return Array.from(root.children).map((n) => document.importNode(n, true));
    }

    // Move a wrapper's presentation onto a child (used when unwrapping or ungrouping).
    function inherit(attrs, child) {
        for (const a of attrs) {
            const name = a.name;
            if (name === 'transform' || name === 'id' || name.startsWith('data-') || name.startsWith('xmlns')) continue;
            if (name === 'opacity') {
                const outer = parseFloat(a.value), own = parseFloat(child.getAttribute('opacity') ?? '1');
                if (Number.isFinite(outer) && Number.isFinite(own)) child.setAttribute('opacity', String(round(outer * own, 1e4)));
            } else if (name === 'style') {
                const own = child.getAttribute('style');
                child.setAttribute('style', own ? `${a.value};${own}` : a.value);
            } else if (name === 'class') {
                child.classList.add(...a.value.split(/\s+/).filter(Boolean));
            } else if (!child.hasAttribute(name)) {
                copyAttr(child, a);
            }
        }
    }

    function refsIn(node, out) {
        for (const el of tree(node)) {
            for (const a of el.attributes) {
                if (/(^|:)href$/i.test(a.name) && a.value.startsWith('#')) out.add(a.value.slice(1));
                for (const m of a.value.matchAll(/url\(\s*['"]?#([^'")\s]+)/g)) out.add(m[1]);
            }
        }
    }

    // Gradients, clips or symbols that live outside the copied elements but are referenced by them.
    function missingDefs(clones, lookup) {
        if (!lookup) return [];
        const have = new Set(), want = new Set(), extra = [];
        for (const c of clones) {
            for (const el of tree(c)) if (el.id) have.add(el.id);
            refsIn(c, want);
        }
        for (const id of want) {
            if (have.has(id)) continue;
            const src = lookup(id);
            if (!src) continue;
            const copy = src.cloneNode(true);
            have.add(id);
            extra.push(copy);
            refsIn(copy, want);
        }
        return extra;
    }

    function stripData(root) {
        for (const el of tree(root)) {
            for (const a of Array.from(el.attributes)) if (a.name.startsWith('data-')) el.removeAttribute(a.name);
        }
    }

    // Standalone SVG text for `elements`; `box` (document units) becomes the 0,0-origin viewBox.
    // opts: { lookup(id) → element, keepData, background }
    function serialize(elements, box, opts = {}) {
        const svg = document.createElementNS(SVG_NS, 'svg');
        const w = round(box.w, 100), h = round(box.h, 100);
        svg.setAttribute('width', w);
        svg.setAttribute('height', h);
        svg.setAttribute('viewBox', `0 0 ${w} ${h}`);
        const add = (node) => {
            svg.appendChild(document.createTextNode('\n  '));
            svg.appendChild(node);
        };
        if (opts.background) {
            const bg = document.createElementNS(SVG_NS, 'rect');
            bg.setAttribute('width', w);
            bg.setAttribute('height', h);
            bg.setAttribute('fill', opts.background);
            add(bg);
        }
        const clones = elements.map((el) => {
            const c = el.cloneNode(true);
            if (box.x || box.y) setMatrix(c, new DOMMatrix().translate(-box.x, -box.y).multiply(matrixOf(el)));
            return c;
        });
        const defs = missingDefs(clones, opts.lookup);
        if (defs.length) {
            const d = document.createElementNS(SVG_NS, 'defs');
            defs.forEach((x) => d.appendChild(x));
            add(d);
        }
        clones.forEach(add);
        svg.appendChild(document.createTextNode('\n'));
        if (!opts.keepData) stripData(svg);
        return new XMLSerializer().serializeToString(svg);
    }

    global.Svgx = { SVG_NS, NON_GRAPHIC, prepare, fragment, serialize, inherit, uniquifyIds, matrixOf, setMatrix, copyAttr };
})(window);
