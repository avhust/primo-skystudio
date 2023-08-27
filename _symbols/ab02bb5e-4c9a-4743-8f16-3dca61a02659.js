// Hero2 - Updated August 27, 2023
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
function element(name) {
    return document.createElement(name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
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
function set_style(node, key, value, important) {
    if (value == null) {
        node.style.removeProperty(key);
    }
    else {
        node.style.setProperty(key, value, important ? 'important' : '');
    }
}
function toggle_class(element, name, toggle) {
    element.classList[toggle ? 'add' : 'remove'](name);
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
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
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

function create_if_block_1(ctx) {
	let a;
	let span;
	let t;

	return {
		c() {
			a = element("a");
			span = element("span");
			t = text("Детальніше");
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			span = claim_element(a_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t = claim_text(span_nodes, "Детальніше");
			span_nodes.forEach(detach);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "svelte-xt9fw9");
			attr(a, "href", "#mainContent");
			attr(a, "class", "svelte-xt9fw9");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, span);
			append_hydration(span, t);
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (341:3) {#if slideno === 0}
function create_if_block(ctx) {
	let t;

	return {
		c() {
			t = text("вул. Залізнична 1А");
		},
		l(nodes) {
			t = claim_text(nodes, "вул. Залізнична 1А");
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

function create_fragment(ctx) {
	let section;
	let picture;
	let source0;
	let t0;
	let source1;
	let t1;
	let img;
	let img_src_value;
	let t2;
	let div5;
	let div0;
	let raw_value = /*texts*/ ctx[1][/*slideno*/ ctx[2]].first + "";
	let t3;
	let div1;
	let t4_value = /*texts*/ ctx[1][/*slideno*/ ctx[2]].second + "";
	let t4;
	let t5;
	let div2;
	let t6;
	let div3;
	let t7;
	let div4;
	let a0;
	let t8;
	let br0;
	let t9;
	let t10;
	let a1;
	let t11;
	let br1;
	let t12;
	let t13;
	let a2;
	let t14;
	let br2;
	let t15;
	let t16;
	let a3;
	let t17;
	let br3;
	let t18;
	let t19;
	let a4;
	let t20;
	let br4;
	let t21;
	let if_block0 = /*texts*/ ctx[1][/*slideno*/ ctx[2]].button && create_if_block_1();
	let if_block1 = /*slideno*/ ctx[2] === 0 && create_if_block();

	return {
		c() {
			section = element("section");
			picture = element("picture");
			source0 = element("source");
			t0 = space();
			source1 = element("source");
			t1 = space();
			img = element("img");
			t2 = space();
			div5 = element("div");
			div0 = element("div");
			t3 = space();
			div1 = element("div");
			t4 = text(t4_value);
			t5 = space();
			div2 = element("div");
			if (if_block0) if_block0.c();
			t6 = space();
			div3 = element("div");
			if (if_block1) if_block1.c();
			t7 = space();
			div4 = element("div");
			a0 = element("a");
			t8 = text("фотозони");
			br0 = element("br");
			t9 = text("Sky Studio");
			t10 = space();
			a1 = element("a");
			t11 = text("наша техніка");
			br1 = element("br");
			t12 = text("та обладнання");
			t13 = space();
			a2 = element("a");
			t14 = text("крила");
			br2 = element("br");
			t15 = text("в оренду");
			t16 = space();
			a3 = element("a");
			t17 = text("аксесуари та");
			br3 = element("br");
			t18 = text(" сукні в оренду");
			t19 = space();
			a4 = element("a");
			t20 = text("про");
			br4 = element("br");
			t21 = text("нашу студію");
			this.h();
		},
		l(nodes) {
			section = claim_element(nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			picture = claim_element(section_nodes, "PICTURE", { class: true });
			var picture_nodes = children(picture);
			source0 = claim_element(picture_nodes, "SOURCE", { type: true, sizes: true, srcset: true });
			t0 = claim_space(picture_nodes);
			source1 = claim_element(picture_nodes, "SOURCE", { type: true, sizes: true, srcset: true });
			t1 = claim_space(picture_nodes);

			img = claim_element(picture_nodes, "IMG", {
				alt: true,
				src: true,
				srcset: true,
				sizes: true,
				height: true,
				width: true,
				style: true,
				class: true
			});

			picture_nodes.forEach(detach);
			t2 = claim_space(section_nodes);
			div5 = claim_element(section_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			div0 = claim_element(div5_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			t3 = claim_space(div5_nodes);
			div1 = claim_element(div5_nodes, "DIV", { class: true, style: true });
			var div1_nodes = children(div1);
			t4 = claim_text(div1_nodes, t4_value);
			div1_nodes.forEach(detach);
			t5 = claim_space(div5_nodes);
			div2 = claim_element(div5_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			if (if_block0) if_block0.l(div2_nodes);
			div2_nodes.forEach(detach);
			t6 = claim_space(div5_nodes);
			div3 = claim_element(div5_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			if (if_block1) if_block1.l(div3_nodes);
			div3_nodes.forEach(detach);
			t7 = claim_space(div5_nodes);
			div4 = claim_element(div5_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			a0 = claim_element(div4_nodes, "A", { href: true, class: true });
			var a0_nodes = children(a0);
			t8 = claim_text(a0_nodes, "фотозони");
			br0 = claim_element(a0_nodes, "BR", {});
			t9 = claim_text(a0_nodes, "Sky Studio");
			a0_nodes.forEach(detach);
			t10 = claim_space(div4_nodes);
			a1 = claim_element(div4_nodes, "A", { href: true, class: true });
			var a1_nodes = children(a1);
			t11 = claim_text(a1_nodes, "наша техніка");
			br1 = claim_element(a1_nodes, "BR", {});
			t12 = claim_text(a1_nodes, "та обладнання");
			a1_nodes.forEach(detach);
			t13 = claim_space(div4_nodes);
			a2 = claim_element(div4_nodes, "A", { href: true, class: true });
			var a2_nodes = children(a2);
			t14 = claim_text(a2_nodes, "крила");
			br2 = claim_element(a2_nodes, "BR", {});
			t15 = claim_text(a2_nodes, "в оренду");
			a2_nodes.forEach(detach);
			t16 = claim_space(div4_nodes);
			a3 = claim_element(div4_nodes, "A", { href: true, class: true });
			var a3_nodes = children(a3);
			t17 = claim_text(a3_nodes, "аксесуари та");
			br3 = claim_element(a3_nodes, "BR", {});
			t18 = claim_text(a3_nodes, " сукні в оренду");
			a3_nodes.forEach(detach);
			t19 = claim_space(div4_nodes);
			a4 = claim_element(div4_nodes, "A", { href: true, class: true });
			var a4_nodes = children(a4);
			t20 = claim_text(a4_nodes, "про");
			br4 = claim_element(a4_nodes, "BR", {});
			t21 = claim_text(a4_nodes, "нашу студію");
			a4_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			section_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(source0, "type", "image/avif");
			attr(source0, "sizes", "100vw");
			attr(source0, "srcset", "\n\t\t\t  " + cdn + /*slides*/ ctx[0][/*slideno*/ ctx[2]].src + "-2x.avif 2128w, \n\t\t\t  " + cdn + /*slides*/ ctx[0][/*slideno*/ ctx[2]].src + "-1x.avif 1419w");
			attr(source1, "type", "image/webp");
			attr(source1, "sizes", "100vw");
			attr(source1, "srcset", "\n\t\t\t  " + cdn + /*slides*/ ctx[0][/*slideno*/ ctx[2]].src + "-2x.webp 2128w, \n\t\t\t  " + cdn + /*slides*/ ctx[0][/*slideno*/ ctx[2]].src + "-1x.webp 1419w");
			attr(img, "alt", "hero");
			if (!src_url_equal(img.src, img_src_value = "" + (cdn + /*slides*/ ctx[0][/*slideno*/ ctx[2]].src + "-1x.jpg"))) attr(img, "src", img_src_value);
			attr(img, "srcset", "\n\t\t\t  " + cdn + /*slides*/ ctx[0][/*slideno*/ ctx[2]].src + "-2x.jpg 2128w, \n\t\t\t  " + cdn + /*slides*/ ctx[0][/*slideno*/ ctx[2]].src + "-1x.jpg 1419w");
			attr(img, "sizes", "100vw");
			attr(img, "height", "1061");
			attr(img, "width", "2126");
			set_style(img, "content-visibility", "auto");
			attr(img, "class", "svelte-xt9fw9");
			set_style(img, "--moveX", /*slides*/ ctx[0][/*slideno*/ ctx[2]].moveMobile.x);
			set_style(img, "--scale", /*slides*/ ctx[0][/*slideno*/ ctx[2]].moveMobile.scale);
			attr(picture, "class", "svelte-xt9fw9");
			set_style(picture, "--brightness", /*slides*/ ctx[0][/*slideno*/ ctx[2]].brightness || '');
			attr(div0, "class", "first svelte-xt9fw9");
			attr(div1, "class", "second svelte-xt9fw9");
			set_style(div1, "--length", /*texts*/ ctx[1][/*slideno*/ ctx[2]].second.length);
			attr(div2, "class", "buttonHero svelte-xt9fw9");
			attr(div3, "class", "premenu svelte-xt9fw9");
			attr(a0, "href", "/fotozony");
			attr(a0, "class", "svelte-xt9fw9");
			toggle_class(a0, "active", /*slideno*/ ctx[2] === 1);
			attr(a1, "href", "/tekhnika");
			attr(a1, "class", "svelte-xt9fw9");
			toggle_class(a1, "active", /*slideno*/ ctx[2] === 2);
			attr(a2, "href", "/kryla");
			attr(a2, "class", "svelte-xt9fw9");
			toggle_class(a2, "active", /*slideno*/ ctx[2] === 3);
			attr(a3, "href", "/sukni");
			attr(a3, "class", "svelte-xt9fw9");
			toggle_class(a3, "active", /*slideno*/ ctx[2] === 4);
			attr(a4, "href", "/pro");
			attr(a4, "class", "svelte-xt9fw9");
			toggle_class(a4, "active", /*slideno*/ ctx[2] === 5);
			attr(div4, "class", "menu svelte-xt9fw9");
			attr(div5, "class", "texts svelte-xt9fw9");
			attr(section, "class", "svelte-xt9fw9");
		},
		m(target, anchor) {
			insert_hydration(target, section, anchor);
			append_hydration(section, picture);
			append_hydration(picture, source0);
			append_hydration(picture, t0);
			append_hydration(picture, source1);
			append_hydration(picture, t1);
			append_hydration(picture, img);
			append_hydration(section, t2);
			append_hydration(section, div5);
			append_hydration(div5, div0);
			div0.innerHTML = raw_value;
			append_hydration(div5, t3);
			append_hydration(div5, div1);
			append_hydration(div1, t4);
			append_hydration(div5, t5);
			append_hydration(div5, div2);
			if (if_block0) if_block0.m(div2, null);
			append_hydration(div5, t6);
			append_hydration(div5, div3);
			if (if_block1) if_block1.m(div3, null);
			append_hydration(div5, t7);
			append_hydration(div5, div4);
			append_hydration(div4, a0);
			append_hydration(a0, t8);
			append_hydration(a0, br0);
			append_hydration(a0, t9);
			append_hydration(div4, t10);
			append_hydration(div4, a1);
			append_hydration(a1, t11);
			append_hydration(a1, br1);
			append_hydration(a1, t12);
			append_hydration(div4, t13);
			append_hydration(div4, a2);
			append_hydration(a2, t14);
			append_hydration(a2, br2);
			append_hydration(a2, t15);
			append_hydration(div4, t16);
			append_hydration(div4, a3);
			append_hydration(a3, t17);
			append_hydration(a3, br3);
			append_hydration(a3, t18);
			append_hydration(div4, t19);
			append_hydration(div4, a4);
			append_hydration(a4, t20);
			append_hydration(a4, br4);
			append_hydration(a4, t21);
		},
		p: noop,
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(section);
			if (if_block0) if_block0.d();
			if (if_block1) if_block1.d();
		}
	};
}

const cdn = 'https://cdn.skystudio.uz.ua/old';

function instance($$self, $$props, $$invalidate) {
	let { props } = $$props;

	const slides = [
		{
			src: '/hero/home',
			height: 706,
			width: 1200,
			brightness: '0.35',
			moveMobile: { x: "88%", scale: "1" }
		},
		{
			src: '/hero/fotozony',
			height: 773,
			width: 1200,
			brightness: '0.35',
			moveMobile: { x: "50%", scale: "1" }
		},
		{
			src: '/hero/tekhnika',
			height: 871,
			width: 1200,
			brightness: '0.35',
			moveMobile: { x: "50%", scale: "1" }
		},
		{
			src: '/hero/kryla',
			height: 824,
			width: 1200,
			brightness: '0.35',
			moveMobile: { x: "50%", scale: "1.2" }
		},
		{
			src: '/hero/sukni',
			height: 801,
			width: 1200,
			brightness: '0.35',
			moveMobile: { x: "50%", scale: "1" }
		},
		{
			src: '/hero/pro',
			height: 889,
			width: 1200,
			brightness: '0.35',
			moveMobile: { x: "50%", scale: "1" }
		}
	];

	const texts = [
		{
			first: 'фотостудія<br/>з крилами',
			second: 'в Ужгороді',
			button: true
		},
		{
			first: '<br/>фотозони',
			second: 'Sky Studio',
			button: true
		},
		{
			first: '<br/>техніка',
			second: 'Sky Studio',
			button: true
		},
		{
			first: '<br/>крила',
			second: 'Sky Studio',
			button: true
		},
		{
			first: 'сукні та<br/>аксесуари',
			second: 'Sky Studio',
			button: true
		},
		{
			first: 'про<br/>нашу',
			second: 'студію',
			button: true
		}
	];

	//let slideno=select_slide ? parseInt(select_slide) : 0
	let slideno = typeof slide_number !== 'undefined'
	? parseInt(slide_number)
	: 0;

	$$self.$$set = $$props => {
		if ('props' in $$props) $$invalidate(3, props = $$props.props);
	};

	return [slides, texts, slideno, props];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { props: 3 });
	}
}

export { Component as default };
