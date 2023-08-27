// Home-Text&News - Updated August 27, 2023
function noop() { }
const identity = x => x;
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
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
function create_slot(definition, ctx, $$scope, fn) {
    if (definition) {
        const slot_ctx = get_slot_context(definition, ctx, $$scope, fn);
        return definition[0](slot_ctx);
    }
}
function get_slot_context(definition, ctx, $$scope, fn) {
    return definition[1] && fn
        ? assign($$scope.ctx.slice(), definition[1](fn(ctx)))
        : $$scope.ctx;
}
function get_slot_changes(definition, $$scope, dirty, fn) {
    if (definition[2] && fn) {
        const lets = definition[2](fn(dirty));
        if ($$scope.dirty === undefined) {
            return lets;
        }
        if (typeof lets === 'object') {
            const merged = [];
            const len = Math.max($$scope.dirty.length, lets.length);
            for (let i = 0; i < len; i += 1) {
                merged[i] = $$scope.dirty[i] | lets[i];
            }
            return merged;
        }
        return $$scope.dirty | lets;
    }
    return $$scope.dirty;
}
function update_slot_base(slot, slot_definition, ctx, $$scope, slot_changes, get_slot_context_fn) {
    if (slot_changes) {
        const slot_context = get_slot_context(slot_definition, ctx, $$scope, get_slot_context_fn);
        slot.p(slot_context, slot_changes);
    }
}
function get_all_dirty_from_scope($$scope) {
    if ($$scope.ctx.length > 32) {
        const dirty = [];
        const length = $$scope.ctx.length / 32;
        for (let i = 0; i < length; i++) {
            dirty[i] = -1;
        }
        return dirty;
    }
    return -1;
}
function action_destroyer(action_result) {
    return action_result && is_function(action_result.destroy) ? action_result.destroy : noop;
}

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
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
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
    return style.sheet;
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
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
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
function toggle_class(element, name, toggle) {
    element.classList[toggle ? 'add' : 'remove'](name);
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { ownerNode } = info.stylesheet;
            // there is no ownerNode if it runs on jsdom.
            if (ownerNode)
                detach(ownerNode);
        });
        managed_styles.clear();
    });
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
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

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
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
const null_transition = { duration: 0 };
function create_in_transition(node, fn, params) {
    const options = { direction: 'in' };
    let config = fn(node, params, options);
    let running = false;
    let animation_name;
    let task;
    let uid = 0;
    function cleanup() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function go() {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        if (css)
            animation_name = create_rule(node, 0, 1, duration, delay, easing, css, uid++);
        tick(0, 1);
        const start_time = now() + delay;
        const end_time = start_time + duration;
        if (task)
            task.abort();
        running = true;
        add_render_callback(() => dispatch(node, true, 'start'));
        task = loop(now => {
            if (running) {
                if (now >= end_time) {
                    tick(1, 0);
                    dispatch(node, true, 'end');
                    cleanup();
                    return running = false;
                }
                if (now >= start_time) {
                    const t = easing((now - start_time) / duration);
                    tick(t, 1 - t);
                }
            }
            return running;
        });
    }
    let started = false;
    return {
        start() {
            if (started)
                return;
            started = true;
            delete_rule(node);
            if (is_function(config)) {
                config = config(options);
                wait().then(go);
            }
            else {
                go();
            }
        },
        invalidate() {
            started = false;
        },
        end() {
            if (running) {
                cleanup();
                running = false;
            }
        }
    };
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

function create_if_block$1(ctx) {
	let picture;

	function select_block_type(ctx, dirty) {
		if (/*x2*/ ctx[6]) return create_if_block_1$1;
		return create_else_block$1;
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
function create_else_block$1(ctx) {
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
function create_if_block_1$1(ctx) {
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
	let if_block = /*image*/ ctx[2] && create_if_block$1(ctx);

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
					if_block = create_if_block$1(ctx);
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
	let { cdn = "" } = $$props;
	let { path = "/i" } = $$props;
	let { image = "" } = $$props;
	let { alt = "placeholder" } = $$props;
	let { height = 200 } = $$props;
	let { width = 200 } = $$props;
	let { x2 = false } = $$props;
	let { loading = "lazy" } = $$props;

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
			$$invalidate(9, format = image.split(".").pop());
		}

		if ($$self.$$.dirty & /*image*/ 4) {
			$$invalidate(8, name = image.split(".").slice(0, -1));
		}
	};

	return [cdn, path, image, alt, height, width, x2, loading, name, format];
}

let Component$2 = class Component extends SvelteComponent {
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
};

const expandable = (node, expanded) => {
    let placeholder = document.createElement("div");
    let slot = node.firstChild ? node.firstChild : node;
    placeholder.style.width = `${node.clientWidth}px`;
    placeholder.style.height = `${node.clientHeight}px`;
    const handleMousedown = () => {
        node.parentElement?.appendChild(placeholder);
        node.dispatchEvent(new CustomEvent('expanding'));
        // TODO Add animation from static to fixed position (with additional element?)
        // const { width, height, x, y } = node.getBoundingClientRect();
        // node.style.left = `${x}px`;
        // node.style.top = `${y}px`;
        // node.style.width = `${width}px`;
        // node.style.height = `${height}px`;
        // console.log(window.innerWidth);
        // console.log(window.innerHeight);
    };
    slot.addEventListener('click', handleMousedown);
    slot.addEventListener('keypress', handleMousedown);
    return {
        update(expanded) {
            if (!expanded && node.parentElement?.contains(placeholder)) {
                node.parentElement?.removeChild(placeholder);
            }
        },
        destroy() {
            slot.removeEventListener('click', handleMousedown);
            slot.removeEventListener('keypress', handleMousedown);
            if (node.parentElement?.contains(placeholder)) {
                node.parentElement?.removeChild(placeholder);
            }
        }
    };
};

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}

/* generated by Svelte v3.59.1 */

function create_else_block(ctx) {
	let current;
	const default_slot_template = /*#slots*/ ctx[8].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[7], null);

	return {
		c() {
			if (default_slot) default_slot.c();
		},
		l(nodes) {
			if (default_slot) default_slot.l(nodes);
		},
		m(target, anchor) {
			if (default_slot) {
				default_slot.m(target, anchor);
			}

			current = true;
		},
		p(ctx, dirty) {
			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 128)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[7],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[7])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[7], dirty, null),
						null
					);
				}
			}
		},
		i(local) {
			if (current) return;
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (default_slot) default_slot.d(detaching);
		}
	};
}

// (22:0) {#if screenWidth > breakpoint}
function create_if_block(ctx) {
	let t0;
	let div;
	let t1;
	let t2;
	let expandable_action;
	let current;
	let mounted;
	let dispose;
	let if_block0 = /*expanded*/ ctx[0] && create_if_block_3(ctx);
	const default_slot_template = /*#slots*/ ctx[8].default;
	const default_slot = create_slot(default_slot_template, ctx, /*$$scope*/ ctx[7], null);
	let if_block1 = /*expanded*/ ctx[0] && /*youtubeVideoId*/ ctx[3] && create_if_block_2(ctx);
	let if_block2 = /*expanded*/ ctx[0] && create_if_block_1(ctx);

	return {
		c() {
			if (if_block0) if_block0.c();
			t0 = space();
			div = element("div");
			if (default_slot) default_slot.c();
			t1 = space();
			if (if_block1) if_block1.c();
			t2 = space();
			if (if_block2) if_block2.c();
			this.h();
		},
		l(nodes) {
			if (if_block0) if_block0.l(nodes);
			t0 = claim_space(nodes);
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			if (default_slot) default_slot.l(div_nodes);
			t1 = claim_space(div_nodes);
			if (if_block1) if_block1.l(div_nodes);
			t2 = claim_space(div_nodes);
			if (if_block2) if_block2.l(div_nodes);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "poster svelte-18ae490");
			toggle_class(div, "expanded", /*expanded*/ ctx[0]);
		},
		m(target, anchor) {
			if (if_block0) if_block0.m(target, anchor);
			insert_hydration(target, t0, anchor);
			insert_hydration(target, div, anchor);

			if (default_slot) {
				default_slot.m(div, null);
			}

			append_hydration(div, t1);
			if (if_block1) if_block1.m(div, null);
			append_hydration(div, t2);
			if (if_block2) if_block2.m(div, null);
			current = true;

			if (!mounted) {
				dispose = [
					action_destroyer(expandable_action = expandable.call(null, div, /*expanded*/ ctx[0])),
					listen(div, "expanding", /*onExpanded*/ ctx[6])
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (/*expanded*/ ctx[0]) {
				if (if_block0) {
					if_block0.p(ctx, dirty);

					if (dirty & /*expanded*/ 1) {
						transition_in(if_block0, 1);
					}
				} else {
					if_block0 = create_if_block_3(ctx);
					if_block0.c();
					transition_in(if_block0, 1);
					if_block0.m(t0.parentNode, t0);
				}
			} else if (if_block0) {
				if_block0.d(1);
				if_block0 = null;
			}

			if (default_slot) {
				if (default_slot.p && (!current || dirty & /*$$scope*/ 128)) {
					update_slot_base(
						default_slot,
						default_slot_template,
						ctx,
						/*$$scope*/ ctx[7],
						!current
						? get_all_dirty_from_scope(/*$$scope*/ ctx[7])
						: get_slot_changes(default_slot_template, /*$$scope*/ ctx[7], dirty, null),
						null
					);
				}
			}

			if (/*expanded*/ ctx[0] && /*youtubeVideoId*/ ctx[3]) {
				if (if_block1) {
					if_block1.p(ctx, dirty);
				} else {
					if_block1 = create_if_block_2(ctx);
					if_block1.c();
					if_block1.m(div, t2);
				}
			} else if (if_block1) {
				if_block1.d(1);
				if_block1 = null;
			}

			if (/*expanded*/ ctx[0]) {
				if (if_block2) {
					if_block2.p(ctx, dirty);
				} else {
					if_block2 = create_if_block_1(ctx);
					if_block2.c();
					if_block2.m(div, null);
				}
			} else if (if_block2) {
				if_block2.d(1);
				if_block2 = null;
			}

			if (expandable_action && is_function(expandable_action.update) && dirty & /*expanded*/ 1) expandable_action.update.call(null, /*expanded*/ ctx[0]);

			if (!current || dirty & /*expanded*/ 1) {
				toggle_class(div, "expanded", /*expanded*/ ctx[0]);
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block0);
			transition_in(default_slot, local);
			current = true;
		},
		o(local) {
			transition_out(default_slot, local);
			current = false;
		},
		d(detaching) {
			if (if_block0) if_block0.d(detaching);
			if (detaching) detach(t0);
			if (detaching) detach(div);
			if (default_slot) default_slot.d(detaching);
			if (if_block1) if_block1.d();
			if (if_block2) if_block2.d();
			mounted = false;
			run_all(dispose);
		}
	};
}

// (23:1) {#if expanded}
function create_if_block_3(ctx) {
	let div;
	let div_intro;
	let mounted;
	let dispose;

	return {
		c() {
			div = element("div");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			children(div).forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "cover svelte-18ae490");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);

			if (!mounted) {
				dispose = [
					listen(div, "keypress", /*offExpanded*/ ctx[5]),
					listen(div, "click", /*offExpanded*/ ctx[5])
				];

				mounted = true;
			}
		},
		p: noop,
		i(local) {
			if (!div_intro) {
				add_render_callback(() => {
					div_intro = create_in_transition(div, fade, { duration: 300 });
					div_intro.start();
				});
			}
		},
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
			mounted = false;
			run_all(dispose);
		}
	};
}

// (33:2) {#if expanded && youtubeVideoId}
function create_if_block_2(ctx) {
	let iframe;
	let iframe_src_value;

	return {
		c() {
			iframe = element("iframe");
			this.h();
		},
		l(nodes) {
			iframe = claim_element(nodes, "IFRAME", {
				class: true,
				src: true,
				title: true,
				frameborder: true,
				allow: true
			});

			children(iframe).forEach(detach);
			this.h();
		},
		h() {
			attr(iframe, "class", "videoIFrame svelte-18ae490");
			if (!src_url_equal(iframe.src, iframe_src_value = "https://www.youtube.com/embed/" + /*youtubeVideoId*/ ctx[3] + "?autoplay=1")) attr(iframe, "src", iframe_src_value);
			attr(iframe, "title", "YouTube video player");
			attr(iframe, "frameborder", "0");
			attr(iframe, "allow", "accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture; web-share");
			iframe.allowFullscreen = true;
		},
		m(target, anchor) {
			insert_hydration(target, iframe, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*youtubeVideoId*/ 8 && !src_url_equal(iframe.src, iframe_src_value = "https://www.youtube.com/embed/" + /*youtubeVideoId*/ ctx[3] + "?autoplay=1")) {
				attr(iframe, "src", iframe_src_value);
			}
		},
		d(detaching) {
			if (detaching) detach(iframe);
		}
	};
}

// (43:2) {#if expanded}
function create_if_block_1(ctx) {
	let div;
	let button;
	let img;
	let img_src_value;
	let mounted;
	let dispose;

	return {
		c() {
			div = element("div");
			button = element("button");
			img = element("img");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			button = claim_element(div_nodes, "BUTTON", { class: true });
			var button_nodes = children(button);
			img = claim_element(button_nodes, "IMG", { alt: true, src: true, class: true });
			button_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(img, "alt", "burger icon");
			if (!src_url_equal(img.src, img_src_value = "" + (/*cdn*/ ctx[1] + "/icons/cross.svg"))) attr(img, "src", img_src_value);
			attr(img, "class", "svelte-18ae490");
			attr(button, "class", "svelte-18ae490");
			attr(div, "class", "closeButton svelte-18ae490");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, button);
			append_hydration(button, img);

			if (!mounted) {
				dispose = [
					listen(div, "keypress", /*offExpanded*/ ctx[5]),
					listen(div, "click", /*offExpanded*/ ctx[5])
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*cdn*/ 2 && !src_url_equal(img.src, img_src_value = "" + (/*cdn*/ ctx[1] + "/icons/cross.svg"))) {
				attr(img, "src", img_src_value);
			}
		},
		d(detaching) {
			if (detaching) detach(div);
			mounted = false;
			run_all(dispose);
		}
	};
}

function create_fragment$1(ctx) {
	let current_block_type_index;
	let if_block;
	let if_block_anchor;
	let current;
	const if_block_creators = [create_if_block, create_else_block];
	const if_blocks = [];

	function select_block_type(ctx, dirty) {
		if (/*screenWidth*/ ctx[4] > /*breakpoint*/ ctx[2]) return 0;
		return 1;
	}

	current_block_type_index = select_block_type(ctx);
	if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_blocks[current_block_type_index].m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
			current = true;
		},
		p(ctx, [dirty]) {
			let previous_block_index = current_block_type_index;
			current_block_type_index = select_block_type(ctx);

			if (current_block_type_index === previous_block_index) {
				if_blocks[current_block_type_index].p(ctx, dirty);
			} else {
				group_outros();

				transition_out(if_blocks[previous_block_index], 1, 1, () => {
					if_blocks[previous_block_index] = null;
				});

				check_outros();
				if_block = if_blocks[current_block_type_index];

				if (!if_block) {
					if_block = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
					if_block.c();
				} else {
					if_block.p(ctx, dirty);
				}

				transition_in(if_block, 1);
				if_block.m(if_block_anchor.parentNode, if_block_anchor);
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block);
			current = true;
		},
		o(local) {
			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if_blocks[current_block_type_index].d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	let { $$slots: slots = {}, $$scope } = $$props;
	let { expanded = false } = $$props;
	let { cdn = "" } = $$props;
	let { breakpoint = false } = $$props;
	let screenWidth = breakpoint;
	let { youtubeVideoId = "" } = $$props;

	function offExpanded() {
		$$invalidate(0, expanded = false);
		document.body.classList.remove("noscroll");
	}

	function onExpanded() {
		$$invalidate(0, expanded = true);
		document.body.classList.add("noscroll");
	}

	onMount(() => {
		$$invalidate(4, screenWidth = window ? window.innerWidth : breakpoint);
	});

	$$self.$$set = $$props => {
		if ('expanded' in $$props) $$invalidate(0, expanded = $$props.expanded);
		if ('cdn' in $$props) $$invalidate(1, cdn = $$props.cdn);
		if ('breakpoint' in $$props) $$invalidate(2, breakpoint = $$props.breakpoint);
		if ('youtubeVideoId' in $$props) $$invalidate(3, youtubeVideoId = $$props.youtubeVideoId);
		if ('$$scope' in $$props) $$invalidate(7, $$scope = $$props.$$scope);
	};

	return [
		expanded,
		cdn,
		breakpoint,
		youtubeVideoId,
		screenWidth,
		offExpanded,
		onExpanded,
		$$scope,
		slots
	];
}

let Component$1 = class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$1, create_fragment$1, safe_not_equal, {
			expanded: 0,
			cdn: 1,
			breakpoint: 2,
			youtubeVideoId: 3
		});
	}
};

/* generated by Svelte v3.59.1 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i].title;
	child_ctx[1] = list[i].text;
	child_ctx[4] = list[i].picture;
	child_ctx[5] = list[i].date;
	return child_ctx;
}

// (263:18) <OldExpandable cdn="https://cdn.skystudio.uz.ua/old">
function create_default_slot(ctx) {
	let oldpicture;
	let current;

	oldpicture = new Component$2({
			props: {
				cdn: "https://cdn.skystudio.uz.ua/old",
				x2: false,
				width: 960,
				heigh: 1280,
				loading: "eager",
				path: "/i/news/" + /*date*/ ctx[5],
				image: /*picture*/ ctx[4]
			}
		});

	return {
		c() {
			create_component(oldpicture.$$.fragment);
		},
		l(nodes) {
			claim_component(oldpicture.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(oldpicture, target, anchor);
			current = true;
		},
		p(ctx, dirty) {
			const oldpicture_changes = {};
			if (dirty & /*news*/ 1) oldpicture_changes.path = "/i/news/" + /*date*/ ctx[5];
			if (dirty & /*news*/ 1) oldpicture_changes.image = /*picture*/ ctx[4];
			oldpicture.$set(oldpicture_changes);
		},
		i(local) {
			if (current) return;
			transition_in(oldpicture.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(oldpicture.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(oldpicture, detaching);
		}
	};
}

// (256:2) {#each news as { title, text, picture, date }}
function create_each_block(ctx) {
	let div4;
	let div0;
	let t0_value = /*title*/ ctx[3] + "";
	let t0;
	let t1;
	let div1;
	let t2_value = /*date*/ ctx[5] + "";
	let t2;
	let t3;
	let div2;
	let raw_value = /*text*/ ctx[1] + "";
	let t4;
	let div3;
	let oldexpandable;
	let current;

	oldexpandable = new Component$1({
			props: {
				cdn: "https://cdn.skystudio.uz.ua/old",
				$$slots: { default: [create_default_slot] },
				$$scope: { ctx }
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
			create_component(oldexpandable.$$.fragment);
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
			claim_component(oldexpandable.$$.fragment, div3_nodes);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "news-title svelte-kwgaw5");
			attr(div1, "class", "news-date svelte-kwgaw5");
			attr(div2, "class", "news-text svelte-kwgaw5");
			attr(div2, "data-sveltekit-reload", "");
			attr(div3, "class", "news-image svelte-kwgaw5");
			attr(div4, "class", "news svelte-kwgaw5");
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
			mount_component(oldexpandable, div3, null);
			current = true;
		},
		p(ctx, dirty) {
			if ((!current || dirty & /*news*/ 1) && t0_value !== (t0_value = /*title*/ ctx[3] + "")) set_data(t0, t0_value);
			if ((!current || dirty & /*news*/ 1) && t2_value !== (t2_value = /*date*/ ctx[5] + "")) set_data(t2, t2_value);
			if ((!current || dirty & /*news*/ 1) && raw_value !== (raw_value = /*text*/ ctx[1] + "")) div2.innerHTML = raw_value;			const oldexpandable_changes = {};

			if (dirty & /*$$scope, news*/ 257) {
				oldexpandable_changes.$$scope = { dirty, ctx };
			}

			oldexpandable.$set(oldexpandable_changes);
		},
		i(local) {
			if (current) return;
			transition_in(oldexpandable.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(oldexpandable.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div4);
			destroy_component(oldexpandable);
		}
	};
}

function create_fragment(ctx) {
	let div8;
	let div7;
	let div0;
	let h3;
	let t0;
	let t1;
	let div1;
	let raw_value = /*text*/ ctx[1].html + "";
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
			div8 = claim_element(nodes, "DIV", { class: true });
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
			attr(h3, "class", "svelte-kwgaw5");
			attr(div0, "class", "title svelte-kwgaw5");
			attr(div1, "class", "text svelte-kwgaw5");
			attr(div2, "class", "news-header svelte-kwgaw5");
			attr(div3, "class", "fader svelte-kwgaw5");
			attr(a, "href", "/novyny#mainContent");
			attr(a, "class", "more svelte-kwgaw5");
			attr(div4, "class", "wrapper svelte-kwgaw5");
			attr(div5, "class", "news-wrapper");
			attr(div6, "class", "secondColumn svelte-kwgaw5");
			attr(div7, "class", "block2Columns svelte-kwgaw5");
			attr(div8, "class", "section-container");
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
			if ((!current || dirty & /*text*/ 2) && raw_value !== (raw_value = /*text*/ ctx[1].html + "")) div1.innerHTML = raw_value;
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

function instance($$self, $$props, $$invalidate) {
	let { props } = $$props;
	let { news } = $$props;
	let { text } = $$props;

	$$self.$$set = $$props => {
		if ('props' in $$props) $$invalidate(2, props = $$props.props);
		if ('news' in $$props) $$invalidate(0, news = $$props.news);
		if ('text' in $$props) $$invalidate(1, text = $$props.text);
	};

	return [news, text, props];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { props: 2, news: 0, text: 1 });
	}
}

export { Component as default };
