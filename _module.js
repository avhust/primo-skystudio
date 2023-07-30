function noop() { }
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function set_style(node, key, value, important) {
    if (value == null) {
        node.style.removeProperty(key);
    }
    else {
        node.style.setProperty(key, value, important ? 'important' : '');
    }
}
function head_selector(nodeId, head) {
    const result = [];
    let started = 0;
    for (const node of head.childNodes) {
        if (node.nodeType === 8 /* comment node */) {
            const comment = node.textContent.trim();
            if (comment === `HEAD_${nodeId}_END`) {
                started -= 1;
                result.push(node);
            }
            else if (comment === `HEAD_${nodeId}_START`) {
                started += 1;
                result.push(node);
            }
        }
        else if (started > 0) {
            result.push(node);
        }
    }
    return result;
}

let current_component;
function set_current_component(component) {
    current_component = component;
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

/* generated by Svelte v3.59.1 */

function create_fragment(ctx) {
	let link0;
	let link0_href_value;
	let link1;
	let link2;
	let link3;
	let link4;
	let link5;
	let link6;
	let link7;
	let link8;
	let link9;
	let link10;
	let link11;
	let link12;
	let link13;
	let meta0;
	let meta1;
	let link14;
	let title_value;
	let meta2;
	let style;
	let t;
	document.title = title_value = /*title*/ ctx[1];

	return {
		c() {
			link0 = element("link");
			link1 = element("link");
			link2 = element("link");
			link3 = element("link");
			link4 = element("link");
			link5 = element("link");
			link6 = element("link");
			link7 = element("link");
			link8 = element("link");
			link9 = element("link");
			link10 = element("link");
			link11 = element("link");
			link12 = element("link");
			link13 = element("link");
			meta0 = element("meta");
			meta1 = element("meta");
			link14 = element("link");
			meta2 = element("meta");
			style = element("style");
			t = text("@font-face {\n\t\t\tfont-family: 'ProximaNova';\n\t\t\tfont-style: normal;\n\t\t\tfont-weight: 300;\n\t\t\tfont-stretch: 100%;\n\t\t\tfont-display: swap;\n\t\t\tsrc: url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Regular.woff2) format('woff2'),\n\t\t\t\turl(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Regular.ttf);\n\t\t}\n\n\t\t@font-face {\n\t\t\tfont-family: 'ProximaNova';\n\t\t\tfont-style: normal;\n\t\t\tfont-weight: 600;\n\t\t\tfont-stretch: 100%;\n\t\t\tfont-display: swap;\n\t\t\tsrc: url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Bold.woff2) format('woff2'),\n\t\t\t\turl(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Bold.ttf);\n\t\t}\n\n\t\t@font-face {\n\t\t\tfont-family: 'ProximaNova';\n\t\t\tfont-style: normal;\n\t\t\tfont-weight: 900;\n\t\t\tfont-stretch: 100%;\n\t\t\tfont-display: swap;\n\t\t\tsrc: url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Black.woff2) format('woff2'),\n\t\t\t\turl(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Black.ttf);\n\t\t}\n\n\t\t/* Bold */\n\t\t/* @font-face {\n\t\t\tfont-family: 'NotoSerif';\n\t\t\tfont-style: normal;\n\t\t\tfont-weight: 700;\n\t\t\tfont-stretch: 100%;\n\t\t\tfont-display: swap;\n\t\t\tsrc: url(https://cdn.skystudio.uz.ua/old/fonts/Noto_Serif/NotoSerif-Bold.ttf);\n\t\t} */\n\t\t@font-face {\n\t\t\tfont-family: 'NotoSerif';\n\t\t\tfont-style: normal;\n\t\t\tfont-weight: 700;\n\t\t\tfont-stretch: 100%;\n\t\t\tfont-display: swap;\n\t\t\tsrc: url(https://cdn.skystudio.uz.ua/old/fonts/Noto_Serif/NotoSerif-Regular.ttf);\n\t\t}\n/* Reset & standardize default styles */\n/*@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;*/\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options\n  --color-accent: #004700;\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 0;\n  --border-color: #e0e1e1;\n  */\n  --color-accent: #FEC93C;\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 0;\n  --border-color: #294c80;\n  \n  \t--darkColor: #294c80;\n\t--lightColor: #2d8fc5;\n\t--accentColor: #FEC93C;\n\t--accentDarkerColor: #FEC93C;\n\t--font1: \"ProximaNova\", sans-serif;\n\t--font2: \"NotoSerif\", serif;\n\n\t--color: #0f0f16;\n\t--colorGray: #b6b6d2;\n\t--zoom: 0.9;\n}\n\nhtml {\n\t/* zoom: var(--zoom); */\n}\n\nhtml,\nbody {\n\n}\n\n\n.noscroll {\n\toverflow: hidden;\n}\n\n\n\n/* Root element (use instead of `body`) */\n#page {\n  zoom: var(--zoom);\n\tscroll-behavior: smooth;\n\tscroll-padding: 6em;\n\tpadding: 0; \n\tmargin: 0;\n\tbackground-color: var(--darkColor);\n\tfont-size: 16px;\n\n  \n  \tcolor: var(--color);\n  \n\n  background: white;\n\n\tfont-size: 16px;\n\tfont-family: var(--font1);\n\tfont-weight: 300;\n}\n#page a {\n\t\ttext-decoration: none;\n\t}\n@media (hover: hover) and (pointer: fine) {\n\t\t#page a:hover {\n\t\t\ttext-decoration: none;\n\t\t}\n\t}\n\n/* Elements */\n.section {\n  max-width: 1200px;\n  margin: 0 auto;\n  \t\tpadding: 3rem 1rem;\n\t\tmargin: 0 auto;\n\t\twidth: auto;\n}\n@media screen and (min-width: 768px) {\n.section {\n\t\t\twidth: calc(100% - 2rem)\n}\n\t\t}\n\na.link {\n  line-height: 1.3;\n\n  border-bottom: 2px solid var(--color-accent);\n  transform: translateY(-2px); /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: 2.5rem;\n  line-height: 1.15;\n\n}\n\n.button {\n  color: white;\n  background: var(--color-accent, rebeccapurple);\n  border-radius: 0;\n  padding: 18px 24px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0;\n}\n\n/* reset */\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent, rebeccapurple);\n  }\n\n/* Content Section */\n.content {\n  max-width: 900px;\n  margin: 0 auto;\n  padding: 3rem 2rem;\n}\n.content p {\n    margin-bottom: 1rem;\n    line-height: 1.5;\n  }\n.content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n.content a.link {\n    line-height: 1.3;\n    font-weight: 500;\n    border-bottom: 2px solid var(--color-accent);\n    transform: translateY(-2px); /* move link back into place */\n    transition: var(--transition, 0.1s border);\n  }\n.content a.link:hover {\n      border-color: transparent;\n    }\n.content h1 {\n    font-size: 3rem;\n    font-weight: 500;\n    line-height: 1.1;\n    margin-bottom: 1.5rem;\n  }\n.content h2 {\n    font-size: 2.5rem;\n    font-weight: 500;\n    margin-bottom: 1rem;\n  }\n.content h3 {\n    font-size: 2rem;\n    font-weight: 500;\n    margin-bottom: 1rem;\n  }\n.content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.content blockquote {\n    padding: 2rem;\n    margin-top: 1.5rem;\n    margin-bottom: 1.5rem;\n    border-left: 5px solid var(--color-accent);\n  }");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-dw9fj2', document.head);

			link0 = claim_element(head_nodes, "LINK", {
				rel: true,
				type: true,
				sizes: true,
				href: true
			});

			link1 = claim_element(head_nodes, "LINK", { rel: true, sizes: true, href: true });
			link2 = claim_element(head_nodes, "LINK", { rel: true, sizes: true, href: true });
			link3 = claim_element(head_nodes, "LINK", { rel: true, sizes: true, href: true });
			link4 = claim_element(head_nodes, "LINK", { rel: true, sizes: true, href: true });
			link5 = claim_element(head_nodes, "LINK", { rel: true, sizes: true, href: true });
			link6 = claim_element(head_nodes, "LINK", { rel: true, sizes: true, href: true });
			link7 = claim_element(head_nodes, "LINK", { rel: true, sizes: true, href: true });
			link8 = claim_element(head_nodes, "LINK", { rel: true, sizes: true, href: true });
			link9 = claim_element(head_nodes, "LINK", { rel: true, sizes: true, href: true });

			link10 = claim_element(head_nodes, "LINK", {
				rel: true,
				type: true,
				sizes: true,
				href: true
			});

			link11 = claim_element(head_nodes, "LINK", {
				rel: true,
				type: true,
				sizes: true,
				href: true
			});

			link12 = claim_element(head_nodes, "LINK", {
				rel: true,
				type: true,
				sizes: true,
				href: true
			});

			link13 = claim_element(head_nodes, "LINK", {
				rel: true,
				type: true,
				sizes: true,
				href: true
			});

			meta0 = claim_element(head_nodes, "META", { name: true, content: true });
			meta1 = claim_element(head_nodes, "META", { name: true, content: true });
			link14 = claim_element(head_nodes, "LINK", { rel: true, href: true });
			meta2 = claim_element(head_nodes, "META", { name: true, content: true });
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t = claim_text(style_nodes, "@font-face {\n\t\t\tfont-family: 'ProximaNova';\n\t\t\tfont-style: normal;\n\t\t\tfont-weight: 300;\n\t\t\tfont-stretch: 100%;\n\t\t\tfont-display: swap;\n\t\t\tsrc: url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Regular.woff2) format('woff2'),\n\t\t\t\turl(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Regular.ttf);\n\t\t}\n\n\t\t@font-face {\n\t\t\tfont-family: 'ProximaNova';\n\t\t\tfont-style: normal;\n\t\t\tfont-weight: 600;\n\t\t\tfont-stretch: 100%;\n\t\t\tfont-display: swap;\n\t\t\tsrc: url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Bold.woff2) format('woff2'),\n\t\t\t\turl(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Bold.ttf);\n\t\t}\n\n\t\t@font-face {\n\t\t\tfont-family: 'ProximaNova';\n\t\t\tfont-style: normal;\n\t\t\tfont-weight: 900;\n\t\t\tfont-stretch: 100%;\n\t\t\tfont-display: swap;\n\t\t\tsrc: url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Black.woff2) format('woff2'),\n\t\t\t\turl(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Black.ttf);\n\t\t}\n\n\t\t/* Bold */\n\t\t/* @font-face {\n\t\t\tfont-family: 'NotoSerif';\n\t\t\tfont-style: normal;\n\t\t\tfont-weight: 700;\n\t\t\tfont-stretch: 100%;\n\t\t\tfont-display: swap;\n\t\t\tsrc: url(https://cdn.skystudio.uz.ua/old/fonts/Noto_Serif/NotoSerif-Bold.ttf);\n\t\t} */\n\t\t@font-face {\n\t\t\tfont-family: 'NotoSerif';\n\t\t\tfont-style: normal;\n\t\t\tfont-weight: 700;\n\t\t\tfont-stretch: 100%;\n\t\t\tfont-display: swap;\n\t\t\tsrc: url(https://cdn.skystudio.uz.ua/old/fonts/Noto_Serif/NotoSerif-Regular.ttf);\n\t\t}\n/* Reset & standardize default styles */\n/*@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;*/\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options\n  --color-accent: #004700;\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 0;\n  --border-color: #e0e1e1;\n  */\n  --color-accent: #FEC93C;\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 0;\n  --border-color: #294c80;\n  \n  \t--darkColor: #294c80;\n\t--lightColor: #2d8fc5;\n\t--accentColor: #FEC93C;\n\t--accentDarkerColor: #FEC93C;\n\t--font1: \"ProximaNova\", sans-serif;\n\t--font2: \"NotoSerif\", serif;\n\n\t--color: #0f0f16;\n\t--colorGray: #b6b6d2;\n\t--zoom: 0.9;\n}\n\nhtml {\n\t/* zoom: var(--zoom); */\n}\n\nhtml,\nbody {\n\n}\n\n\n.noscroll {\n\toverflow: hidden;\n}\n\n\n\n/* Root element (use instead of `body`) */\n#page {\n  zoom: var(--zoom);\n\tscroll-behavior: smooth;\n\tscroll-padding: 6em;\n\tpadding: 0; \n\tmargin: 0;\n\tbackground-color: var(--darkColor);\n\tfont-size: 16px;\n\n  \n  \tcolor: var(--color);\n  \n\n  background: white;\n\n\tfont-size: 16px;\n\tfont-family: var(--font1);\n\tfont-weight: 300;\n}\n#page a {\n\t\ttext-decoration: none;\n\t}\n@media (hover: hover) and (pointer: fine) {\n\t\t#page a:hover {\n\t\t\ttext-decoration: none;\n\t\t}\n\t}\n\n/* Elements */\n.section {\n  max-width: 1200px;\n  margin: 0 auto;\n  \t\tpadding: 3rem 1rem;\n\t\tmargin: 0 auto;\n\t\twidth: auto;\n}\n@media screen and (min-width: 768px) {\n.section {\n\t\t\twidth: calc(100% - 2rem)\n}\n\t\t}\n\na.link {\n  line-height: 1.3;\n\n  border-bottom: 2px solid var(--color-accent);\n  transform: translateY(-2px); /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: 2.5rem;\n  line-height: 1.15;\n\n}\n\n.button {\n  color: white;\n  background: var(--color-accent, rebeccapurple);\n  border-radius: 0;\n  padding: 18px 24px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0;\n}\n\n/* reset */\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent, rebeccapurple);\n  }\n\n/* Content Section */\n.content {\n  max-width: 900px;\n  margin: 0 auto;\n  padding: 3rem 2rem;\n}\n.content p {\n    margin-bottom: 1rem;\n    line-height: 1.5;\n  }\n.content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n.content a.link {\n    line-height: 1.3;\n    font-weight: 500;\n    border-bottom: 2px solid var(--color-accent);\n    transform: translateY(-2px); /* move link back into place */\n    transition: var(--transition, 0.1s border);\n  }\n.content a.link:hover {\n      border-color: transparent;\n    }\n.content h1 {\n    font-size: 3rem;\n    font-weight: 500;\n    line-height: 1.1;\n    margin-bottom: 1.5rem;\n  }\n.content h2 {\n    font-size: 2.5rem;\n    font-weight: 500;\n    margin-bottom: 1rem;\n  }\n.content h3 {\n    font-size: 2rem;\n    font-weight: 500;\n    margin-bottom: 1rem;\n  }\n.content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.content blockquote {\n    padding: 2rem;\n    margin-top: 1.5rem;\n    margin-bottom: 1.5rem;\n    border-left: 5px solid var(--color-accent);\n  }");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(link0, "rel", "icon");
			attr(link0, "type", "image/png");
			attr(link0, "sizes", "32x32");
			attr(link0, "href", link0_href_value = /*favicon*/ ctx[0].url);
			attr(link1, "rel", "apple-touch-icon");
			attr(link1, "sizes", "57x57");
			attr(link1, "href", "https://cdn.skystudio.uz.ua/old/favicon/apple-icon-57x57.png");
			attr(link2, "rel", "apple-touch-icon");
			attr(link2, "sizes", "60x60");
			attr(link2, "href", "https://cdn.skystudio.uz.ua/old/favicon/apple-icon-60x60.png");
			attr(link3, "rel", "apple-touch-icon");
			attr(link3, "sizes", "72x72");
			attr(link3, "href", "https://cdn.skystudio.uz.ua/old/favicon/apple-icon-72x72.png");
			attr(link4, "rel", "apple-touch-icon");
			attr(link4, "sizes", "76x76");
			attr(link4, "href", "https://cdn.skystudio.uz.ua/old/favicon/apple-icon-76x76.png");
			attr(link5, "rel", "apple-touch-icon");
			attr(link5, "sizes", "114x114");
			attr(link5, "href", "https://cdn.skystudio.uz.ua/old/favicon/apple-icon-114x114.png");
			attr(link6, "rel", "apple-touch-icon");
			attr(link6, "sizes", "120x120");
			attr(link6, "href", "https://cdn.skystudio.uz.ua/old/favicon/apple-icon-120x120.png");
			attr(link7, "rel", "apple-touch-icon");
			attr(link7, "sizes", "144x144");
			attr(link7, "href", "https://cdn.skystudio.uz.ua/old/favicon/apple-icon-144x144.png");
			attr(link8, "rel", "apple-touch-icon");
			attr(link8, "sizes", "152x152");
			attr(link8, "href", "https://cdn.skystudio.uz.ua/old/favicon/apple-icon-152x152.png");
			attr(link9, "rel", "apple-touch-icon");
			attr(link9, "sizes", "180x180");
			attr(link9, "href", "https://cdn.skystudio.uz.ua/old/favicon/apple-icon-180x180.png");
			attr(link10, "rel", "icon");
			attr(link10, "type", "image/png");
			attr(link10, "sizes", "192x192");
			attr(link10, "href", "https://cdn.skystudio.uz.ua/old/favicon/android-icon-192x192.png");
			attr(link11, "rel", "icon");
			attr(link11, "type", "image/png");
			attr(link11, "sizes", "32x32");
			attr(link11, "href", "https://cdn.skystudio.uz.ua/old/favicon/favicon-32x32.png");
			attr(link12, "rel", "icon");
			attr(link12, "type", "image/png");
			attr(link12, "sizes", "96x96");
			attr(link12, "href", "https://cdn.skystudio.uz.ua/old/favicon/favicon-96x96.png");
			attr(link13, "rel", "icon");
			attr(link13, "type", "image/png");
			attr(link13, "sizes", "16x16");
			attr(link13, "href", "https://cdn.skystudio.uz.ua/old/favicon/favicon-16x16.png");
			attr(meta0, "name", "theme-color");
			attr(meta0, "content", "#2d8fc5");
			attr(meta1, "name", "viewport");
			attr(meta1, "content", "width=device-width,initial-scale=1");
			attr(link14, "rel", "apple-touch-icon");
			attr(link14, "href", "https://cdn.skystudio.uz.ua/old/favicon/apple-touch-icon.png");
			attr(meta2, "name", "description");
			attr(meta2, "content", /*description*/ ctx[2]);
		},
		m(target, anchor) {
			append_hydration(document.head, link0);
			append_hydration(document.head, link1);
			append_hydration(document.head, link2);
			append_hydration(document.head, link3);
			append_hydration(document.head, link4);
			append_hydration(document.head, link5);
			append_hydration(document.head, link6);
			append_hydration(document.head, link7);
			append_hydration(document.head, link8);
			append_hydration(document.head, link9);
			append_hydration(document.head, link10);
			append_hydration(document.head, link11);
			append_hydration(document.head, link12);
			append_hydration(document.head, link13);
			append_hydration(document.head, meta0);
			append_hydration(document.head, meta1);
			append_hydration(document.head, link14);
			append_hydration(document.head, meta2);
			append_hydration(document.head, style);
			append_hydration(style, t);
		},
		p(ctx, [dirty]) {
			if (dirty & /*favicon*/ 1 && link0_href_value !== (link0_href_value = /*favicon*/ ctx[0].url)) {
				attr(link0, "href", link0_href_value);
			}

			if (dirty & /*title*/ 2 && title_value !== (title_value = /*title*/ ctx[1])) {
				document.title = title_value;
			}

			if (dirty & /*description*/ 4) {
				attr(meta2, "content", /*description*/ ctx[2]);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			detach(link0);
			detach(link1);
			detach(link2);
			detach(link3);
			detach(link4);
			detach(link5);
			detach(link6);
			detach(link7);
			detach(link8);
			detach(link9);
			detach(link10);
			detach(link11);
			detach(link12);
			detach(link13);
			detach(meta0);
			detach(meta1);
			detach(link14);
			detach(meta2);
			detach(style);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(1, title = $$props.title);
		if ('description' in $$props) $$invalidate(2, description = $$props.description);
	};

	return [favicon, title, description];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { favicon: 0, title: 1, description: 2 });
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$1(ctx) {
	let div3;
	let div2;
	let div1;
	let div0;
	let t0;
	let a;
	let span;
	let t1_value = /*button*/ ctx[1].label + "";
	let t1;
	let a_href_value;

	return {
		c() {
			div3 = element("div");
			div2 = element("div");
			div1 = element("div");
			div0 = element("div");
			t0 = space();
			a = element("a");
			span = element("span");
			t1 = text(t1_value);
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t0 = claim_space(div1_nodes);
			a = claim_element(div1_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			span = claim_element(a_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t1 = claim_text(span_nodes, t1_value);
			span_nodes.forEach(detach);
			a_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "text svelte-nhwolt");
			attr(span, "class", "svelte-nhwolt");
			attr(a, "href", a_href_value = /*button*/ ctx[1].url);
			attr(a, "class", "svelte-nhwolt");
			attr(div1, "class", "buttonWrapper svelte-nhwolt");
			attr(div2, "class", "infoLine toRight svelte-nhwolt");
			attr(div3, "class", "section");
			attr(div3, "id", "section-e63ef93d");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div2);
			append_hydration(div2, div1);
			append_hydration(div1, div0);
			div0.innerHTML = /*heading*/ ctx[0];
			append_hydration(div1, t0);
			append_hydration(div1, a);
			append_hydration(a, span);
			append_hydration(span, t1);
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) div0.innerHTML = /*heading*/ ctx[0];			if (dirty & /*button*/ 2 && t1_value !== (t1_value = /*button*/ ctx[1].label + "")) set_data(t1, t1_value);

			if (dirty & /*button*/ 2 && a_href_value !== (a_href_value = /*button*/ ctx[1].url)) {
				attr(a, "href", a_href_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div3);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { heading } = $$props;
	let { button } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(2, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(3, title = $$props.title);
		if ('description' in $$props) $$invalidate(4, description = $$props.description);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('button' in $$props) $$invalidate(1, button = $$props.button);
	};

	return [heading, button, favicon, title, description];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$1, create_fragment$1, safe_not_equal, {
			favicon: 2,
			title: 3,
			description: 4,
			heading: 0,
			button: 1
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_if_block(ctx) {
	let picture;

	function select_block_type(ctx, dirty) {
		if (/*x2*/ ctx[6]) return create_if_block_1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			picture = element("picture");
			if_block.c();
		},
		l(nodes) {
			picture = claim_element(nodes, "PICTURE", {});
			var picture_nodes = children(picture);
			if_block.l(picture_nodes);
			picture_nodes.forEach(detach);
		},
		m(target, anchor) {
			insert_hydration(target, picture, anchor);
			if_block.m(picture, null);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(picture, null);
				}
			}
		},
		d(detaching) {
			if (detaching) detach(picture);
			if_block.d();
		}
	};
}

// (35:2) {:else}
function create_else_block(ctx) {
	let source0;
	let source0_srcset_value;
	let t0;
	let source1;
	let source1_srcset_value;
	let t1;
	let img;
	let img_src_value;
	let img_srcset_value;

	return {
		c() {
			source0 = element("source");
			t0 = space();
			source1 = element("source");
			t1 = space();
			img = element("img");
			this.h();
		},
		l(nodes) {
			source0 = claim_element(nodes, "SOURCE", { type: true, srcset: true });
			t0 = claim_space(nodes);
			source1 = claim_element(nodes, "SOURCE", { type: true, srcset: true });
			t1 = claim_space(nodes);

			img = claim_element(nodes, "IMG", {
				alt: true,
				src: true,
				srcset: true,
				height: true,
				width: true,
				loading: true,
				decoding: true
			});

			this.h();
		},
		h() {
			attr(source0, "type", "image/avif");
			attr(source0, "srcset", source0_srcset_value = "" + (/*cdn*/ ctx[0] + /*path*/ ctx[1] + "/avif/" + /*name*/ ctx[8] + ".avif"));
			attr(source1, "type", "image/webp");
			attr(source1, "srcset", source1_srcset_value = "" + (/*cdn*/ ctx[0] + /*path*/ ctx[1] + "/webp/" + /*name*/ ctx[8] + ".webp"));
			attr(img, "alt", /*alt*/ ctx[3]);
			if (!src_url_equal(img.src, img_src_value = "" + (/*cdn*/ ctx[0] + /*path*/ ctx[1] + "/" + /*format*/ ctx[9] + "/" + /*name*/ ctx[8] + "." + /*format*/ ctx[9]))) attr(img, "src", img_src_value);
			attr(img, "srcset", img_srcset_value = "" + (/*cdn*/ ctx[0] + /*path*/ ctx[1] + "/" + /*format*/ ctx[9] + "/" + /*name*/ ctx[8] + "." + /*format*/ ctx[9]));
			attr(img, "height", /*height*/ ctx[4]);
			attr(img, "width", /*width*/ ctx[5]);
			attr(img, "loading", /*loading*/ ctx[7]);
			attr(img, "decoding", "async");
		},
		m(target, anchor) {
			insert_hydration(target, source0, anchor);
			insert_hydration(target, t0, anchor);
			insert_hydration(target, source1, anchor);
			insert_hydration(target, t1, anchor);
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*cdn, path, name*/ 259 && source0_srcset_value !== (source0_srcset_value = "" + (/*cdn*/ ctx[0] + /*path*/ ctx[1] + "/avif/" + /*name*/ ctx[8] + ".avif"))) {
				attr(source0, "srcset", source0_srcset_value);
			}

			if (dirty & /*cdn, path, name*/ 259 && source1_srcset_value !== (source1_srcset_value = "" + (/*cdn*/ ctx[0] + /*path*/ ctx[1] + "/webp/" + /*name*/ ctx[8] + ".webp"))) {
				attr(source1, "srcset", source1_srcset_value);
			}

			if (dirty & /*alt*/ 8) {
				attr(img, "alt", /*alt*/ ctx[3]);
			}

			if (dirty & /*cdn, path, format, name*/ 771 && !src_url_equal(img.src, img_src_value = "" + (/*cdn*/ ctx[0] + /*path*/ ctx[1] + "/" + /*format*/ ctx[9] + "/" + /*name*/ ctx[8] + "." + /*format*/ ctx[9]))) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*cdn, path, format, name*/ 771 && img_srcset_value !== (img_srcset_value = "" + (/*cdn*/ ctx[0] + /*path*/ ctx[1] + "/" + /*format*/ ctx[9] + "/" + /*name*/ ctx[8] + "." + /*format*/ ctx[9]))) {
				attr(img, "srcset", img_srcset_value);
			}

			if (dirty & /*height*/ 16) {
				attr(img, "height", /*height*/ ctx[4]);
			}

			if (dirty & /*width*/ 32) {
				attr(img, "width", /*width*/ ctx[5]);
			}

			if (dirty & /*loading*/ 128) {
				attr(img, "loading", /*loading*/ ctx[7]);
			}
		},
		d(detaching) {
			if (detaching) detach(source0);
			if (detaching) detach(t0);
			if (detaching) detach(source1);
			if (detaching) detach(t1);
			if (detaching) detach(img);
		}
	};
}

// (17:2) {#if x2}
function create_if_block_1(ctx) {
	let source0;
	let source0_srcset_value;
	let t0;
	let source1;
	let source1_srcset_value;
	let t1;
	let img;
	let img_src_value;
	let img_srcset_value;

	return {
		c() {
			source0 = element("source");
			t0 = space();
			source1 = element("source");
			t1 = space();
			img = element("img");
			this.h();
		},
		l(nodes) {
			source0 = claim_element(nodes, "SOURCE", { type: true, srcset: true });
			t0 = claim_space(nodes);
			source1 = claim_element(nodes, "SOURCE", { type: true, srcset: true });
			t1 = claim_space(nodes);

			img = claim_element(nodes, "IMG", {
				alt: true,
				src: true,
				srcset: true,
				height: true,
				width: true,
				loading: true,
				decoding: true
			});

			this.h();
		},
		h() {
			attr(source0, "type", "image/avif");
			attr(source0, "srcset", source0_srcset_value = "" + (/*cdn*/ ctx[0] + /*path*/ ctx[1] + "/avif/" + /*name*/ ctx[8] + "-1x.avif 1x, " + /*cdn*/ ctx[0] + /*path*/ ctx[1] + "/avif/" + /*name*/ ctx[8] + ".avif 2x"));
			attr(source1, "type", "image/webp");
			attr(source1, "srcset", source1_srcset_value = "" + (/*cdn*/ ctx[0] + /*path*/ ctx[1] + "/webp/" + /*name*/ ctx[8] + "-1x.webp 1x, " + /*cdn*/ ctx[0] + /*path*/ ctx[1] + "/webp/" + /*name*/ ctx[8] + ".webp 2x"));
			attr(img, "alt", /*alt*/ ctx[3]);
			if (!src_url_equal(img.src, img_src_value = "" + (/*cdn*/ ctx[0] + /*path*/ ctx[1] + "/" + /*format*/ ctx[9] + "/" + /*name*/ ctx[8] + "." + /*format*/ ctx[9]))) attr(img, "src", img_src_value);
			attr(img, "srcset", img_srcset_value = "" + (/*cdn*/ ctx[0] + /*path*/ ctx[1] + "/" + /*format*/ ctx[9] + "/" + /*name*/ ctx[8] + "-1x." + /*format*/ ctx[9] + " 1x, " + /*cdn*/ ctx[0] + /*path*/ ctx[1] + "/" + /*format*/ ctx[9] + "/" + /*name*/ ctx[8] + "." + /*format*/ ctx[9] + " 2x"));
			attr(img, "height", /*height*/ ctx[4]);
			attr(img, "width", /*width*/ ctx[5]);
			attr(img, "loading", /*loading*/ ctx[7]);
			attr(img, "decoding", "async");
		},
		m(target, anchor) {
			insert_hydration(target, source0, anchor);
			insert_hydration(target, t0, anchor);
			insert_hydration(target, source1, anchor);
			insert_hydration(target, t1, anchor);
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*cdn, path, name*/ 259 && source0_srcset_value !== (source0_srcset_value = "" + (/*cdn*/ ctx[0] + /*path*/ ctx[1] + "/avif/" + /*name*/ ctx[8] + "-1x.avif 1x, " + /*cdn*/ ctx[0] + /*path*/ ctx[1] + "/avif/" + /*name*/ ctx[8] + ".avif 2x"))) {
				attr(source0, "srcset", source0_srcset_value);
			}

			if (dirty & /*cdn, path, name*/ 259 && source1_srcset_value !== (source1_srcset_value = "" + (/*cdn*/ ctx[0] + /*path*/ ctx[1] + "/webp/" + /*name*/ ctx[8] + "-1x.webp 1x, " + /*cdn*/ ctx[0] + /*path*/ ctx[1] + "/webp/" + /*name*/ ctx[8] + ".webp 2x"))) {
				attr(source1, "srcset", source1_srcset_value);
			}

			if (dirty & /*alt*/ 8) {
				attr(img, "alt", /*alt*/ ctx[3]);
			}

			if (dirty & /*cdn, path, format, name*/ 771 && !src_url_equal(img.src, img_src_value = "" + (/*cdn*/ ctx[0] + /*path*/ ctx[1] + "/" + /*format*/ ctx[9] + "/" + /*name*/ ctx[8] + "." + /*format*/ ctx[9]))) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*cdn, path, format, name*/ 771 && img_srcset_value !== (img_srcset_value = "" + (/*cdn*/ ctx[0] + /*path*/ ctx[1] + "/" + /*format*/ ctx[9] + "/" + /*name*/ ctx[8] + "-1x." + /*format*/ ctx[9] + " 1x, " + /*cdn*/ ctx[0] + /*path*/ ctx[1] + "/" + /*format*/ ctx[9] + "/" + /*name*/ ctx[8] + "." + /*format*/ ctx[9] + " 2x"))) {
				attr(img, "srcset", img_srcset_value);
			}

			if (dirty & /*height*/ 16) {
				attr(img, "height", /*height*/ ctx[4]);
			}

			if (dirty & /*width*/ 32) {
				attr(img, "width", /*width*/ ctx[5]);
			}

			if (dirty & /*loading*/ 128) {
				attr(img, "loading", /*loading*/ ctx[7]);
			}
		},
		d(detaching) {
			if (detaching) detach(source0);
			if (detaching) detach(t0);
			if (detaching) detach(source1);
			if (detaching) detach(t1);
			if (detaching) detach(img);
		}
	};
}

function create_fragment$2(ctx) {
	let if_block_anchor;
	let if_block = /*image*/ ctx[2] && create_if_block(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*image*/ ctx[2]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let format;
	let name;
	let { cdn = '' } = $$props;
	let { path = '/i' } = $$props;
	let { image = '' } = $$props;
	let { alt = 'placeholder' } = $$props;
	let { height = 200 } = $$props;
	let { width = 200 } = $$props;
	let { x2 = false } = $$props;
	let { loading = 'lazy' } = $$props;

	$$self.$$set = $$props => {
		if ('cdn' in $$props) $$invalidate(0, cdn = $$props.cdn);
		if ('path' in $$props) $$invalidate(1, path = $$props.path);
		if ('image' in $$props) $$invalidate(2, image = $$props.image);
		if ('alt' in $$props) $$invalidate(3, alt = $$props.alt);
		if ('height' in $$props) $$invalidate(4, height = $$props.height);
		if ('width' in $$props) $$invalidate(5, width = $$props.width);
		if ('x2' in $$props) $$invalidate(6, x2 = $$props.x2);
		if ('loading' in $$props) $$invalidate(7, loading = $$props.loading);
	};

	$$self.$$.update = () => {
		if ($$self.$$.dirty & /*image*/ 4) {
			 $$invalidate(9, format = image.split('.').pop());
		}

		if ($$self.$$.dirty & /*image*/ 4) {
			 $$invalidate(8, name = image.split('.').slice(0, -1));
		}
	};

	return [cdn, path, image, alt, height, width, x2, loading, name, format];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$2, safe_not_equal, {
			cdn: 0,
			path: 1,
			image: 2,
			alt: 3,
			height: 4,
			width: 5,
			x2: 6,
			loading: 7
		});
	}
}

/* generated by Svelte v3.59.1 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[1] = list[i].title;
	child_ctx[2] = list[i].text;
	child_ctx[5] = list[i].picture;
	child_ctx[6] = list[i].date;
	return child_ctx;
}

// (258:2) {#each news as { title, text, picture, date }}
function create_each_block(ctx) {
	let div4;
	let div0;
	let t0_value = /*title*/ ctx[1] + "";
	let t0;
	let t1;
	let div1;
	let t2_value = /*date*/ ctx[6] + "";
	let t2;
	let t3;
	let div2;
	let raw_value = /*text*/ ctx[2] + "";
	let t4;
	let div3;
	let picture;
	let current;

	picture = new Component$2({
			props: {
				cdn: "https://cdn.skystudio.uz.ua/old",
				x2: false,
				width: 960,
				heigh: 1280,
				loading: "eager",
				path: "/i/news/" + /*date*/ ctx[6],
				image: /*picture*/ ctx[5]
			}
		});

	return {
		c() {
			div4 = element("div");
			div0 = element("div");
			t0 = text(t0_value);
			t1 = space();
			div1 = element("div");
			t2 = text(t2_value);
			t3 = space();
			div2 = element("div");
			t4 = space();
			div3 = element("div");
			create_component(picture.$$.fragment);
			this.h();
		},
		l(nodes) {
			div4 = claim_element(nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			div0 = claim_element(div4_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			t0 = claim_text(div0_nodes, t0_value);
			div0_nodes.forEach(detach);
			t1 = claim_space(div4_nodes);
			div1 = claim_element(div4_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			t2 = claim_text(div1_nodes, t2_value);
			div1_nodes.forEach(detach);
			t3 = claim_space(div4_nodes);

			div2 = claim_element(div4_nodes, "DIV", {
				class: true,
				"data-sveltekit-reload": true
			});

			var div2_nodes = children(div2);
			div2_nodes.forEach(detach);
			t4 = claim_space(div4_nodes);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			claim_component(picture.$$.fragment, div3_nodes);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "news-title svelte-jltnxf");
			attr(div1, "class", "news-date svelte-jltnxf");
			attr(div2, "class", "news-text svelte-jltnxf");
			attr(div2, "data-sveltekit-reload", "");
			attr(div3, "class", "news-image svelte-jltnxf");
			attr(div4, "class", "news svelte-jltnxf");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, div0);
			append_hydration(div0, t0);
			append_hydration(div4, t1);
			append_hydration(div4, div1);
			append_hydration(div1, t2);
			append_hydration(div4, t3);
			append_hydration(div4, div2);
			div2.innerHTML = raw_value;
			append_hydration(div4, t4);
			append_hydration(div4, div3);
			mount_component(picture, div3, null);
			current = true;
		},
		p(ctx, dirty) {
			if ((!current || dirty & /*news*/ 1) && t0_value !== (t0_value = /*title*/ ctx[1] + "")) set_data(t0, t0_value);
			if ((!current || dirty & /*news*/ 1) && t2_value !== (t2_value = /*date*/ ctx[6] + "")) set_data(t2, t2_value);
			if ((!current || dirty & /*news*/ 1) && raw_value !== (raw_value = /*text*/ ctx[2] + "")) div2.innerHTML = raw_value;			const picture_changes = {};
			if (dirty & /*news*/ 1) picture_changes.path = "/i/news/" + /*date*/ ctx[6];
			if (dirty & /*news*/ 1) picture_changes.image = /*picture*/ ctx[5];
			picture.$set(picture_changes);
		},
		i(local) {
			if (current) return;
			transition_in(picture.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(picture.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div4);
			destroy_component(picture);
		}
	};
}

function create_fragment$3(ctx) {
	let div8;
	let div7;
	let div0;
	let h3;
	let t0;
	let t1;
	let div1;
	let raw_value = /*text*/ ctx[2].html + "";
	let t2;
	let div6;
	let div5;
	let div4;
	let div2;
	let t3;
	let t4;
	let t5;
	let div3;
	let t6;
	let a;
	let t7;
	let current;
	let each_value = /*news*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div8 = element("div");
			div7 = element("div");
			div0 = element("div");
			h3 = element("h3");
			t0 = text("Sky Studio");
			t1 = space();
			div1 = element("div");
			t2 = space();
			div6 = element("div");
			div5 = element("div");
			div4 = element("div");
			div2 = element("div");
			t3 = text("Новини");
			t4 = space();

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t5 = space();
			div3 = element("div");
			t6 = space();
			a = element("a");
			t7 = text("Всі новини");
			this.h();
		},
		l(nodes) {
			div8 = claim_element(nodes, "DIV", { class: true, id: true });
			var div8_nodes = children(div8);
			div7 = claim_element(div8_nodes, "DIV", { class: true });
			var div7_nodes = children(div7);
			div0 = claim_element(div7_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h3 = claim_element(div0_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t0 = claim_text(h3_nodes, "Sky Studio");
			h3_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t1 = claim_space(div7_nodes);
			div1 = claim_element(div7_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div1_nodes.forEach(detach);
			t2 = claim_space(div7_nodes);
			div6 = claim_element(div7_nodes, "DIV", { class: true });
			var div6_nodes = children(div6);
			div5 = claim_element(div6_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			div4 = claim_element(div5_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			div2 = claim_element(div4_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			t3 = claim_text(div2_nodes, "Новини");
			div2_nodes.forEach(detach);
			t4 = claim_space(div4_nodes);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div4_nodes);
			}

			t5 = claim_space(div4_nodes);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			children(div3).forEach(detach);
			t6 = claim_space(div4_nodes);
			a = claim_element(div4_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t7 = claim_text(a_nodes, "Всі новини");
			a_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			div6_nodes.forEach(detach);
			div7_nodes.forEach(detach);
			div8_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h3, "class", "svelte-jltnxf");
			attr(div0, "class", "title svelte-jltnxf");
			attr(div1, "class", "text svelte-jltnxf");
			attr(div2, "class", "news-header svelte-jltnxf");
			attr(div3, "class", "fader svelte-jltnxf");
			attr(a, "href", "/novyny#mainContent");
			attr(a, "class", "more svelte-jltnxf");
			attr(div4, "class", "wrapper svelte-jltnxf");
			attr(div5, "class", "news-wrapper");
			attr(div6, "class", "secondColumn svelte-jltnxf");
			attr(div7, "class", "block2Columns svelte-jltnxf");
			attr(div8, "class", "section");
			attr(div8, "id", "section-d2e87603");
		},
		m(target, anchor) {
			insert_hydration(target, div8, anchor);
			append_hydration(div8, div7);
			append_hydration(div7, div0);
			append_hydration(div0, h3);
			append_hydration(h3, t0);
			append_hydration(div7, t1);
			append_hydration(div7, div1);
			div1.innerHTML = raw_value;
			append_hydration(div7, t2);
			append_hydration(div7, div6);
			append_hydration(div6, div5);
			append_hydration(div5, div4);
			append_hydration(div4, div2);
			append_hydration(div2, t3);
			append_hydration(div4, t4);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div4, null);
				}
			}

			append_hydration(div4, t5);
			append_hydration(div4, div3);
			append_hydration(div4, t6);
			append_hydration(div4, a);
			append_hydration(a, t7);
			current = true;
		},
		p(ctx, [dirty]) {
			if ((!current || dirty & /*text*/ 4) && raw_value !== (raw_value = /*text*/ ctx[2].html + "")) div1.innerHTML = raw_value;
			if (dirty & /*news*/ 1) {
				each_value = /*news*/ ctx[0];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(div4, t5);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			if (detaching) detach(div8);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$3($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { news } = $$props;
	let { text } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(1, title = $$props.title);
		if ('description' in $$props) $$invalidate(4, description = $$props.description);
		if ('news' in $$props) $$invalidate(0, news = $$props.news);
		if ('text' in $$props) $$invalidate(2, text = $$props.text);
	};

	return [news, title, text, favicon, description];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			favicon: 3,
			title: 1,
			description: 4,
			news: 0,
			text: 2
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$4(ctx) {
	let div4;
	let div3;
	let div0;
	let h3;
	let t0;
	let t1;
	let div1;
	let raw_value = /*text*/ ctx[1].html + "";
	let t2;
	let div2;
	let picture;
	let source0;
	let t3;
	let source1;
	let t4;
	let img;
	let img_src_value;

	return {
		c() {
			div4 = element("div");
			div3 = element("div");
			div0 = element("div");
			h3 = element("h3");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			div1 = element("div");
			t2 = space();
			div2 = element("div");
			picture = element("picture");
			source0 = element("source");
			t3 = space();
			source1 = element("source");
			t4 = space();
			img = element("img");
			this.h();
		},
		l(nodes) {
			div4 = claim_element(nodes, "DIV", { class: true, id: true });
			var div4_nodes = children(div4);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div0 = claim_element(div3_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			h3 = claim_element(div0_nodes, "H3", { class: true });
			var h3_nodes = children(h3);
			t0 = claim_text(h3_nodes, /*heading*/ ctx[0]);
			h3_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t1 = claim_space(div3_nodes);
			div1 = claim_element(div3_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			div1_nodes.forEach(detach);
			t2 = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			picture = claim_element(div2_nodes, "PICTURE", { class: true });
			var picture_nodes = children(picture);
			source0 = claim_element(picture_nodes, "SOURCE", { type: true, srcset: true });
			t3 = claim_space(picture_nodes);
			source1 = claim_element(picture_nodes, "SOURCE", { type: true, srcset: true });
			t4 = claim_space(picture_nodes);

			img = claim_element(picture_nodes, "IMG", {
				alt: true,
				src: true,
				srcset: true,
				width: true,
				height: true,
				loading: true,
				decoding: true,
				class: true
			});

			picture_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h3, "class", "svelte-1mxbfeb");
			attr(div0, "class", "title svelte-1mxbfeb");
			attr(div1, "class", "text svelte-1mxbfeb");
			attr(source0, "type", "image/avif");
			attr(source0, "srcset", "https://cdn.skystudio.uz.ua/old/i/home/avif/home1-1x.avif 1x, https://cdn.skystudio.uz.ua/old/i/home/avif/home1.avif 2x");
			attr(source1, "type", "image/webp");
			attr(source1, "srcset", "https://cdn.skystudio.uz.ua/old/i/home/webp/home1-1x.webp 1x, https://cdn.skystudio.uz.ua/old/i/home/webp/home1.webp 2x");
			attr(img, "alt", "SkyStudio фотостудія в Ужгороді");
			if (!src_url_equal(img.src, img_src_value = "https://cdn.skystudio.uz.ua/old/i/home/jpg/home1.jpg")) attr(img, "src", img_src_value);
			attr(img, "srcset", "https://cdn.skystudio.uz.ua/old/i/home/jpg/home1-1x.jpg 1x, https://cdn.skystudio.uz.ua/old/i/home/jpg/home1.jpg 2x");
			attr(img, "width", "800");
			attr(img, "height", "1199");
			attr(img, "loading", "lazy");
			attr(img, "decoding", "async");
			attr(img, "class", "svelte-1mxbfeb");
			attr(picture, "class", "svelte-1mxbfeb");
			attr(div2, "class", "image svelte-1mxbfeb");
			attr(div3, "class", "blockWithImageAndButton svelte-1mxbfeb");
			attr(div4, "class", "section");
			attr(div4, "id", "section-21e44ccf");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, div3);
			append_hydration(div3, div0);
			append_hydration(div0, h3);
			append_hydration(h3, t0);
			append_hydration(div3, t1);
			append_hydration(div3, div1);
			div1.innerHTML = raw_value;
			append_hydration(div3, t2);
			append_hydration(div3, div2);
			append_hydration(div2, picture);
			append_hydration(picture, source0);
			append_hydration(picture, t3);
			append_hydration(picture, source1);
			append_hydration(picture, t4);
			append_hydration(picture, img);
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);
			if (dirty & /*text*/ 2 && raw_value !== (raw_value = /*text*/ ctx[1].html + "")) div1.innerHTML = raw_value;		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div4);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { heading } = $$props;
	let { text } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(2, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(3, title = $$props.title);
		if ('description' in $$props) $$invalidate(4, description = $$props.description);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('text' in $$props) $$invalidate(1, text = $$props.text);
	};

	return [heading, text, favicon, title, description];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$4, create_fragment$4, safe_not_equal, {
			favicon: 2,
			title: 3,
			description: 4,
			heading: 0,
			text: 1
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$5(ctx) {
	let div;
	let iframe;
	let iframe_src_value;

	return {
		c() {
			div = element("div");
			iframe = element("iframe");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true, id: true });
			var div_nodes = children(div);

			iframe = claim_element(div_nodes, "IFRAME", {
				src: true,
				style: true,
				width: true,
				height: true,
				frameborder: true,
				scrolling: true,
				title: true,
				class: true
			});

			children(iframe).forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(iframe.src, iframe_src_value = "https://calendar.google.com/calendar/embed?height=600&wkst=2&bgcolor=%23ffffff&ctz=Europe%2FKiev&mode=MONTH&showTitle=0&showDate=1&showPrint=0&showTabs=1&showCalendars=0&showTz=0&title=SkyStudio%20%D0%91%D1%80%D0%BE%D0%BD%D1%8C&src=c2t5c3R1ZGlvLnV6QGdtYWlsLmNvbQ&color=%234285F4")) attr(iframe, "src", iframe_src_value);
			set_style(iframe, "border", "0");
			attr(iframe, "width", "800");
			attr(iframe, "height", "600");
			attr(iframe, "frameborder", "0");
			attr(iframe, "scrolling", "no");
			attr(iframe, "title", "Google Calendar");
			attr(iframe, "class", "svelte-wo908b");
			attr(div, "class", "section");
			attr(div, "id", "section-fe6920b8");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, iframe);
		},
		p: noop,
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(1, title = $$props.title);
		if ('description' in $$props) $$invalidate(2, description = $$props.description);
	};

	return [favicon, title, description];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$5, create_fragment$5, safe_not_equal, { favicon: 0, title: 1, description: 2 });
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$6(ctx) {
	let div3;
	let div2;
	let div0;
	let t0;
	let t1;
	let div1;
	let a0;
	let img0;
	let img0_src_value;
	let t2;
	let a1;
	let img1;
	let img1_src_value;
	let t3;
	let a2;
	let img2;
	let img2_src_value;

	return {
		c() {
			div3 = element("div");
			div2 = element("div");
			div0 = element("div");
			t0 = text("Для бронювання фотостудії звʼяжіться з нами:");
			t1 = space();
			div1 = element("div");
			a0 = element("a");
			img0 = element("img");
			t2 = space();
			a1 = element("a");
			img1 = element("img");
			t3 = space();
			a2 = element("a");
			img2 = element("img");
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, id: true });
			var div3_nodes = children(div3);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			t0 = claim_text(div0_nodes, "Для бронювання фотостудії звʼяжіться з нами:");
			div0_nodes.forEach(detach);
			t1 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a0 = claim_element(div1_nodes, "A", { rel: true, href: true, class: true });
			var a0_nodes = children(a0);
			img0 = claim_element(a0_nodes, "IMG", { alt: true, src: true, class: true });
			a0_nodes.forEach(detach);
			t2 = claim_space(div1_nodes);

			a1 = claim_element(div1_nodes, "A", {
				target: true,
				rel: true,
				href: true,
				class: true
			});

			var a1_nodes = children(a1);
			img1 = claim_element(a1_nodes, "IMG", { alt: true, src: true, class: true });
			a1_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);

			a2 = claim_element(div1_nodes, "A", {
				target: true,
				rel: true,
				href: true,
				class: true
			});

			var a2_nodes = children(a2);
			img2 = claim_element(a2_nodes, "IMG", { alt: true, src: true, class: true });
			a2_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "text svelte-sabpsk");
			attr(img0, "alt", "phone");
			if (!src_url_equal(img0.src, img0_src_value = "data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='1em' height='1em' viewBox='0 0 36 36'%3E%3Cpath fill='%23ffffff' d='M15.22 20.64a20.37 20.37 0 0 0 7.4 4.79l3.77-3a.67.67 0 0 1 .76 0l7 4.51a2 2 0 0 1 .33 3.18l-3.28 3.24a4 4 0 0 1-3.63 1.07a35.09 35.09 0 0 1-17.15-9A33.79 33.79 0 0 1 1.15 8.6a3.78 3.78 0 0 1 1.1-3.55l3.4-3.28a2 2 0 0 1 3.12.32L13.43 9a.63.63 0 0 1 0 .75l-3.07 3.69a19.75 19.75 0 0 0 4.86 7.2Z' class='clr-i-solid clr-i-solid-path-1'/%3E%3Cpath fill='none' d='M0 0h36v36H0z'/%3E%3C/svg%3E")) attr(img0, "src", img0_src_value);
			attr(img0, "class", "svelte-sabpsk");
			attr(a0, "rel", "noreferrer");
			attr(a0, "href", "tel:+380950889787");
			attr(a0, "class", "svelte-sabpsk");
			attr(img1, "alt", "instagram icon");
			if (!src_url_equal(img1.src, img1_src_value = "data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='1em' height='1em' viewBox='0 0 24 24'%3E%3Cpath fill='%23ffffff' d='M13.028 2.001a78.82 78.82 0 0 1 2.189.022l.194.007c.224.008.445.018.712.03c1.064.05 1.79.218 2.427.465c.66.254 1.216.598 1.772 1.154a4.908 4.908 0 0 1 1.153 1.771c.247.637.415 1.364.465 2.428c.012.266.022.488.03.712l.006.194a79 79 0 0 1 .023 2.188l.001.746v1.31a78.836 78.836 0 0 1-.023 2.189l-.006.194c-.008.224-.018.445-.03.712c-.05 1.064-.22 1.79-.466 2.427a4.884 4.884 0 0 1-1.153 1.772a4.915 4.915 0 0 1-1.772 1.153c-.637.247-1.363.415-2.427.465c-.267.012-.488.022-.712.03l-.194.006a79 79 0 0 1-2.189.023l-.746.001h-1.309a78.836 78.836 0 0 1-2.189-.023l-.194-.006a60.64 60.64 0 0 1-.712-.03c-1.064-.05-1.79-.22-2.428-.466a4.89 4.89 0 0 1-1.771-1.153a4.904 4.904 0 0 1-1.154-1.772c-.247-.637-.415-1.363-.465-2.427a74.367 74.367 0 0 1-.03-.712l-.005-.194A79.053 79.053 0 0 1 2 13.028v-2.056a78.82 78.82 0 0 1 .022-2.188l.007-.194c.008-.224.018-.446.03-.712c.05-1.065.218-1.79.465-2.428A4.88 4.88 0 0 1 3.68 3.68a4.897 4.897 0 0 1 1.77-1.155c.638-.247 1.363-.415 2.428-.465l.712-.03l.194-.005A79.053 79.053 0 0 1 10.972 2h2.056Zm-1.028 5A5 5 0 1 0 12 17a5 5 0 0 0 0-10Zm0 2A3 3 0 1 1 12.001 15a3 3 0 0 1 0-6Zm5.25-3.5a1.25 1.25 0 0 0 0 2.498a1.25 1.25 0 0 0 0-2.5Z'/%3E%3C/svg%3E")) attr(img1, "src", img1_src_value);
			attr(img1, "class", "svelte-sabpsk");
			set_style(img1, "--size", `1.5rem`);
			attr(a1, "target", "_blank");
			attr(a1, "rel", "noreferrer");
			attr(a1, "href", "https://www.instagram.com/sky_studio_uzh/");
			attr(a1, "class", "svelte-sabpsk");
			attr(img2, "alt", "telegram icon");
			if (!src_url_equal(img2.src, img2_src_value = "data:image/svg+xml,%3Csvg xmlns='http://www.w3.org/2000/svg' width='1em' height='1em' viewBox='0 0 48 48'%3E%3Cpath fill='white' d='M41.42 7.309s3.885-1.515 3.56 2.164c-.107 1.515-1.078 6.818-1.834 12.553l-2.59 16.99s-.216 2.489-2.159 2.922c-1.942.432-4.856-1.515-5.396-1.948c-.432-.325-8.094-5.195-10.792-7.575c-.756-.65-1.62-1.948.108-3.463L33.648 18.13c1.295-1.298 2.59-4.328-2.806-.649l-15.11 10.28s-1.727 1.083-4.964.109l-7.016-2.165s-2.59-1.623 1.835-3.246c10.793-5.086 24.068-10.28 35.831-15.15Z'/%3E%3C/svg%3E")) attr(img2, "src", img2_src_value);
			attr(img2, "class", "svelte-sabpsk");
			set_style(img2, "--size", `1.4rem`);
			attr(a2, "target", "_blank");
			attr(a2, "rel", "noreferrer");
			attr(a2, "href", "https://t.me/macwings");
			attr(a2, "class", "svelte-sabpsk");
			attr(div1, "class", "contactUs svelte-sabpsk");
			attr(div2, "class", "contactUsLine svelte-sabpsk");
			attr(div3, "class", "section");
			attr(div3, "id", "section-8029bd1a");
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div2);
			append_hydration(div2, div0);
			append_hydration(div0, t0);
			append_hydration(div2, t1);
			append_hydration(div2, div1);
			append_hydration(div1, a0);
			append_hydration(a0, img0);
			append_hydration(div1, t2);
			append_hydration(div1, a1);
			append_hydration(a1, img1);
			append_hydration(div1, t3);
			append_hydration(div1, a2);
			append_hydration(a2, img2);
		},
		p: noop,
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div3);
		}
	};
}

function instance$6($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(1, title = $$props.title);
		if ('description' in $$props) $$invalidate(2, description = $$props.description);
	};

	return [favicon, title, description];
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$6, create_fragment$6, safe_not_equal, { favicon: 0, title: 1, description: 2 });
	}
}

/* generated by Svelte v3.59.1 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[5] = list[i].item;
	return child_ctx;
}

// (107:3) {#each links as {item}}
function create_each_block$1(ctx) {
	let a;
	let t_value = /*item*/ ctx[5].label + "";
	let t;
	let a_href_value;
	let a_title_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true, title: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "footer svelte-1fs83g");
			attr(a, "href", a_href_value = /*item*/ ctx[5].url);
			attr(a, "title", a_title_value = /*item*/ ctx[5].label);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*links*/ 2 && t_value !== (t_value = /*item*/ ctx[5].label + "")) set_data(t, t_value);

			if (dirty & /*links*/ 2 && a_href_value !== (a_href_value = /*item*/ ctx[5].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*links*/ 2 && a_title_value !== (a_title_value = /*item*/ ctx[5].label)) {
				attr(a, "title", a_title_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$7(ctx) {
	let div4;
	let footer;
	let div3;
	let div0;
	let a0;
	let img;
	let img_src_value;
	let t0;
	let div1;
	let t1;
	let div2;
	let a1;
	let t2;
	let a1_href_value;
	let br0;
	let t3;
	let br1;
	let t4;
	let t5_value = new Date().getFullYear() + "";
	let t5;
	let each_value = /*links*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	return {
		c() {
			div4 = element("div");
			footer = element("footer");
			div3 = element("div");
			div0 = element("div");
			a0 = element("a");
			img = element("img");
			t0 = space();
			div1 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t1 = space();
			div2 = element("div");
			a1 = element("a");
			t2 = text(/*email*/ ctx[0]);
			br0 = element("br");
			t3 = text("\n\t\t\t\"Sky Studio – Фотостудія з крилами в Ужгороді\"");
			br1 = element("br");
			t4 = text("\n\t\t\tПри копіюванні матеріалів із сайту посилання обов'язкове. Усі права захищені © ");
			t5 = text(t5_value);
			this.h();
		},
		l(nodes) {
			div4 = claim_element(nodes, "DIV", { class: true, id: true });
			var div4_nodes = children(div4);
			footer = claim_element(div4_nodes, "FOOTER", { class: true });
			var footer_nodes = children(footer);
			div3 = claim_element(footer_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div0 = claim_element(div3_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			a0 = claim_element(div0_nodes, "A", { href: true, class: true });
			var a0_nodes = children(a0);
			img = claim_element(a0_nodes, "IMG", { src: true, alt: true, class: true });
			a0_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t0 = claim_space(div3_nodes);
			div1 = claim_element(div3_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div1_nodes);
			}

			div1_nodes.forEach(detach);
			t1 = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			a1 = claim_element(div2_nodes, "A", { href: true, class: true });
			var a1_nodes = children(a1);
			t2 = claim_text(a1_nodes, /*email*/ ctx[0]);
			a1_nodes.forEach(detach);
			br0 = claim_element(div2_nodes, "BR", {});
			t3 = claim_text(div2_nodes, "\n\t\t\t\"Sky Studio – Фотостудія з крилами в Ужгороді\"");
			br1 = claim_element(div2_nodes, "BR", {});
			t4 = claim_text(div2_nodes, "\n\t\t\tПри копіюванні матеріалів із сайту посилання обов'язкове. Усі права захищені © ");
			t5 = claim_text(div2_nodes, t5_value);
			div2_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			footer_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = "https://cdn.skystudio.uz.ua/old/skystudio_logo.svg")) attr(img, "src", img_src_value);
			attr(img, "alt", "Logo SkyStudio");
			attr(img, "class", "svelte-1fs83g");
			attr(a0, "href", "/");
			attr(a0, "class", "svelte-1fs83g");
			attr(div0, "class", "logo");
			attr(div1, "class", "nav svelte-1fs83g");
			attr(a1, "href", a1_href_value = "mailto:" + /*email*/ ctx[0]);
			attr(a1, "class", "svelte-1fs83g");
			attr(div2, "class", "info svelte-1fs83g");
			attr(div3, "class", "container svelte-1fs83g");
			attr(footer, "class", "svelte-1fs83g");
			attr(div4, "class", "section");
			attr(div4, "id", "section-11d6b08b");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, footer);
			append_hydration(footer, div3);
			append_hydration(div3, div0);
			append_hydration(div0, a0);
			append_hydration(a0, img);
			append_hydration(div3, t0);
			append_hydration(div3, div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div1, null);
				}
			}

			append_hydration(div3, t1);
			append_hydration(div3, div2);
			append_hydration(div2, a1);
			append_hydration(a1, t2);
			append_hydration(div2, br0);
			append_hydration(div2, t3);
			append_hydration(div2, br1);
			append_hydration(div2, t4);
			append_hydration(div2, t5);
		},
		p(ctx, [dirty]) {
			if (dirty & /*links*/ 2) {
				each_value = /*links*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div1, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if (dirty & /*email*/ 1) set_data(t2, /*email*/ ctx[0]);

			if (dirty & /*email*/ 1 && a1_href_value !== (a1_href_value = "mailto:" + /*email*/ ctx[0])) {
				attr(a1, "href", a1_href_value);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div4);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$7($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { email } = $$props;
	let { links } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(2, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(3, title = $$props.title);
		if ('description' in $$props) $$invalidate(4, description = $$props.description);
		if ('email' in $$props) $$invalidate(0, email = $$props.email);
		if ('links' in $$props) $$invalidate(1, links = $$props.links);
	};

	return [email, links, favicon, title, description];
}

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$7, create_fragment$7, safe_not_equal, {
			favicon: 2,
			title: 3,
			description: 4,
			email: 0,
			links: 1
		});
	}
}

/* generated by Svelte v3.59.1 */

function instance$8($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(1, title = $$props.title);
		if ('description' in $$props) $$invalidate(2, description = $$props.description);
	};

	return [favicon, title, description];
}

class Component$8 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$8, null, safe_not_equal, { favicon: 0, title: 1, description: 2 });
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$8(ctx) {
	let component_0;
	let t0;
	let component_1;
	let t1;
	let component_2;
	let t2;
	let component_3;
	let t3;
	let component_4;
	let t4;
	let component_5;
	let t5;
	let component_6;
	let t6;
	let component_7;
	let current;

	component_0 = new Component({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "BillionTrees Project",
				description: "We're on a mission to save the trees"
			}
		});

	component_1 = new Component$1({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "BillionTrees Project",
				description: "We're on a mission to save the trees",
				heading: "Переглянути&nbsp;фотозони",
				button: {
					"url": "/fotozony#mainContent",
					"label": "Переглянути"
				}
			}
		});

	component_2 = new Component$3({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "BillionTrees Project",
				description: "We're on a mission to save the trees",
				news: [
					{
						"date": "22.07.2023",
						"text": "Зона для немовлят з фруктами - вже доступна до бронювання. Зазвичай дітки люблять бавитися в воді, тому ми організували цю зону саме для них👼🏻",
						"title": "Нова фотозона",
						"picture": "photo1.jpg"
					},
					{
						"date": "20.07.2023",
						"text": "Це справжня новинка для фотографів - постійне кольорове світло Godox🔥 Можна виставити будь-який колір спектру для вашої зйомки. Входить у вартість оренди😉",
						"title": "Нове кольорове світло",
						"picture": "photo1.jpg"
					},
					{
						"date": "18.07.2023",
						"text": "В нашій студії зʼявились сукні на маму і дитину в стилі Барбі. Також маємо дві пари жіночих босоніжок в рожевому кольорі. Образи вже доступні до оренди",
						"title": "Барбі",
						"picture": "photo1.jpg"
					}
				],
				text: {
					"html": "<p>це фотостудія в Ужгороді, де ви можете орендувати крила янгола для зйомки. Ми працюємо з 1 грудня 2022 року. Засновниця студії Євгенія своїми руками створює крила янгола і робить все можливе для того, щоб ваша зйомка була на висоті. В нас є все необхідне для ідеальних фото. Переконайтеся самі 🙂</p>\n<h3 id=\"h3\">Студія пропонує до ваших послуг:</h3></h3>\n<ul>\n<li>4 фотозони</li>\n<li>циклорама 3х6м</li>\n<li>вінілові фотофони</li>\n<li>світло Godox</li>\n<li>гнучкі дзеркала</li>\n<li>вентилятор</li>\n<li>кольорові фільтри</li>\n<li>пілон</li>\n<li>інше</li>\n</ul>\n<h3 id=\"h3-1\">Додатково є можливість орендувати:</h3></h3>\n<ul>\n<li>крила янгола різних кольорів і розмірів</li>\n<li>вечірні сукні</li>\n<li>аксесуари</li>\n</ul>",
					"markdown": "це фотостудія в Ужгороді, де ви можете орендувати крила янгола для зйомки. Ми працюємо з 1 грудня 2022 року. Засновниця студії Євгенія своїми руками створює крила янгола і робить все можливе для того, щоб ваша зйомка була на висоті. В нас є все необхідне для ідеальних фото. Переконайтеся самі 🙂\n\n### Студія пропонує до ваших послуг:</h3>\n\n* 4 фотозони\n* циклорама 3х6м\n* вінілові фотофони\n* світло Godox\n* гнучкі дзеркала\n* вентилятор\n* кольорові фільтри\n* пілон\n* інше\n\n### Додатково є можливість орендувати:</h3>\n\n* крила янгола різних кольорів і розмірів\n* вечірні сукні\n* аксесуари\n"
				}
			}
		});

	component_3 = new Component$4({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "BillionTrees Project",
				description: "We're on a mission to save the trees",
				heading: "Правила оренди студії",
				text: {
					"html": "<ol>\n<li>Оренда студії відбувається без передоплати. Будь ласка, про зміни попереджуйте заздалегідь.</li>\n<li>У студії є змінне взуття на 6 людей. Якщо людей буде більше, вам треба подбати про своє змінне взуття. У нас на підлозі коврове покриття, тому спокійно можна бути в шкарпетках.</li>\n<li>Якщо ви будете фотографуватись у взутті, воно обовʼязково має бути чистим!</li>\n<li>Вся студія бронюється за вами лише за умови роботи одного фотографа. Якщо працює два фотографа паралельно на різних зонах, оплата подвоюється.</li>\n<li>Чай, кава - безкоштовні. Капучино - за наявності молока :)</li>\n<li>В разі пошкодження майна вам необхідно повністю компенсувати збитки. Витрати оплачуються вами відразу. Шукаємо ринкову ціну пошкодженої речі при вас.</li>\n<li>Якщо ви плануєте зйомку з тваринами чи просто приходите з ними, попереджуйте про їх наявність завчасно та узгоджуйте це питання з нами.</li>\n<li>Відверті зйомки — це добре, але категорично заборонені зйомки порнографічного характеру.</li>\n</ol>\n<h3 id=\"skystudio\">Дякуємо за розуміння! З радістю чекаємо вас в Sky Studio.</h3>",
					"markdown": "1. Оренда студії відбувається без передоплати. Будь ласка, про зміни попереджуйте заздалегідь.\n2. У студії є змінне взуття на 6 людей. Якщо людей буде більше, вам треба подбати про своє змінне взуття. У нас на підлозі коврове покриття, тому спокійно можна бути в шкарпетках.\n3. Якщо ви будете фотографуватись у взутті, воно обовʼязково має бути чистим!\n4. Вся студія бронюється за вами лише за умови роботи одного фотографа. Якщо працює два фотографа паралельно на різних зонах, оплата подвоюється.\n5. Чай, кава - безкоштовні. Капучино - за наявності молока :)\n6. В разі пошкодження майна вам необхідно повністю компенсувати збитки. Витрати оплачуються вами відразу. Шукаємо ринкову ціну пошкодженої речі при вас.\n7. Якщо ви плануєте зйомку з тваринами чи просто приходите з ними, попереджуйте про їх наявність завчасно та узгоджуйте це питання з нами.\n8. Відверті зйомки — це добре, але категорично заборонені зйомки порнографічного характеру.\n\n### Дякуємо за розуміння! З радістю чекаємо вас в Sky Studio."
				}
			}
		});

	component_4 = new Component$5({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "BillionTrees Project",
				description: "We're on a mission to save the trees"
			}
		});

	component_5 = new Component$6({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "BillionTrees Project",
				description: "We're on a mission to save the trees"
			}
		});

	component_6 = new Component$7({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "Sky Studio – Фотостудія з крилами в Ужгороді",
				description: "We're on a mission to save the trees",
				email: "contact@skystudio.uz.ua",
				links: [
					{
						"item": { "url": "/", "label": "Головна" }
					},
					{
						"item": { "url": "/", "label": "Фотозони" }
					},
					{
						"item": { "url": "/", "label": "Техніка" }
					},
					{ "item": { "url": "/", "label": "Крила" } },
					{ "item": { "url": "/", "label": "Сукні" } },
					{
						"item": { "url": "/", "label": "Про нас" }
					}
				]
			}
		});

	component_7 = new Component$8({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "BillionTrees Project",
				description: "We're on a mission to save the trees"
			}
		});

	return {
		c() {
			create_component(component_0.$$.fragment);
			t0 = space();
			create_component(component_1.$$.fragment);
			t1 = space();
			create_component(component_2.$$.fragment);
			t2 = space();
			create_component(component_3.$$.fragment);
			t3 = space();
			create_component(component_4.$$.fragment);
			t4 = space();
			create_component(component_5.$$.fragment);
			t5 = space();
			create_component(component_6.$$.fragment);
			t6 = space();
			create_component(component_7.$$.fragment);
		},
		l(nodes) {
			claim_component(component_0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(component_1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(component_2.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(component_3.$$.fragment, nodes);
			t3 = claim_space(nodes);
			claim_component(component_4.$$.fragment, nodes);
			t4 = claim_space(nodes);
			claim_component(component_5.$$.fragment, nodes);
			t5 = claim_space(nodes);
			claim_component(component_6.$$.fragment, nodes);
			t6 = claim_space(nodes);
			claim_component(component_7.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(component_0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(component_1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(component_2, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(component_3, target, anchor);
			insert_hydration(target, t3, anchor);
			mount_component(component_4, target, anchor);
			insert_hydration(target, t4, anchor);
			mount_component(component_5, target, anchor);
			insert_hydration(target, t5, anchor);
			mount_component(component_6, target, anchor);
			insert_hydration(target, t6, anchor);
			mount_component(component_7, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(component_0.$$.fragment, local);
			transition_in(component_1.$$.fragment, local);
			transition_in(component_2.$$.fragment, local);
			transition_in(component_3.$$.fragment, local);
			transition_in(component_4.$$.fragment, local);
			transition_in(component_5.$$.fragment, local);
			transition_in(component_6.$$.fragment, local);
			transition_in(component_7.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			transition_out(component_5.$$.fragment, local);
			transition_out(component_6.$$.fragment, local);
			transition_out(component_7.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(component_0, detaching);
			if (detaching) detach(t0);
			destroy_component(component_1, detaching);
			if (detaching) detach(t1);
			destroy_component(component_2, detaching);
			if (detaching) detach(t2);
			destroy_component(component_3, detaching);
			if (detaching) detach(t3);
			destroy_component(component_4, detaching);
			if (detaching) detach(t4);
			destroy_component(component_5, detaching);
			if (detaching) detach(t5);
			destroy_component(component_6, detaching);
			if (detaching) detach(t6);
			destroy_component(component_7, detaching);
		}
	};
}

class Component$9 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$8, safe_not_equal, {});
	}
}

export default Component$9;
