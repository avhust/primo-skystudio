// Header - Updated August 27, 2023
function noop() { }
const identity = x => x;
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
function action_destroyer(action_result) {
    return action_result && is_function(action_result.destroy) ? action_result.destroy : noop;
}
function split_css_unit(value) {
    const split = typeof value === 'string' && value.match(/^\s*(-?[\d.]+)([^\s]*)\s*$/);
    return split ? [parseFloat(split[1]), split[2] || 'px'] : [value, 'px'];
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

const globals = (typeof window !== 'undefined'
    ? window
    : typeof globalThis !== 'undefined'
        ? globalThis
        : global);

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
function create_out_transition(node, fn, params) {
    const options = { direction: 'out' };
    let config = fn(node, params, options);
    let running = true;
    let animation_name;
    const group = outros;
    group.r += 1;
    function go() {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        if (css)
            animation_name = create_rule(node, 1, 0, duration, delay, easing, css);
        const start_time = now() + delay;
        const end_time = start_time + duration;
        add_render_callback(() => dispatch(node, false, 'start'));
        loop(now => {
            if (running) {
                if (now >= end_time) {
                    tick(0, 1);
                    dispatch(node, false, 'end');
                    if (!--group.r) {
                        // this will result in `end()` being called,
                        // so we don't need to clean up here
                        run_all(group.c);
                    }
                    return false;
                }
                if (now >= start_time) {
                    const t = easing((now - start_time) / duration);
                    tick(1 - t, t);
                }
            }
            return running;
        });
    }
    if (is_function(config)) {
        wait().then(() => {
            // @ts-ignore
            config = config(options);
            go();
        });
    }
    else {
        go();
    }
    return {
        end(reset) {
            if (reset && config.tick) {
                config.tick(1, 0);
            }
            if (running) {
                if (animation_name)
                    delete_rule(node, animation_name);
                running = false;
            }
        }
    };
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

function circIn(t) {
    return 1.0 - Math.sqrt(1.0 - t * t);
}
function circOut(t) {
    return Math.sqrt(1 - --t * t);
}
function cubicOut(t) {
    const f = t - 1.0;
    return f * f * f + 1.0;
}

function fly(node, { delay = 0, duration = 400, easing = cubicOut, x = 0, y = 0, opacity = 0 } = {}) {
    const style = getComputedStyle(node);
    const target_opacity = +style.opacity;
    const transform = style.transform === 'none' ? '' : style.transform;
    const od = target_opacity * (1 - opacity);
    const [xValue, xUnit] = split_css_unit(x);
    const [yValue, yUnit] = split_css_unit(y);
    return {
        delay,
        duration,
        easing,
        css: (t, u) => `
			transform: ${transform} translate(${(1 - t) * xValue}${xUnit}, ${(1 - t) * yValue}${yUnit});
			opacity: ${target_opacity - (od * u)}`
    };
}

/* generated by Svelte v3.59.1 */

const { window: window_1 } = globals;

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[12] = list[i].item;
	child_ctx[14] = i;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[12] = list[i].item;
	child_ctx[14] = i;
	return child_ctx;
}

// (356:0) {#if openMenu}
function create_if_block_1(ctx) {
	let div6;
	let div0;
	let button;
	let img0;
	let img0_src_value;
	let t0;
	let div4;
	let div1;
	let a0;
	let img1;
	let img1_src_value;
	let t1;
	let ul;
	let t2;
	let div2;
	let a1;
	let img2;
	let img2_src_value;
	let t3;
	let a2;
	let img3;
	let img3_src_value;
	let t4;
	let a3;
	let img4;
	let img4_src_value;
	let t5;
	let a4;
	let img5;
	let img5_src_value;
	let t6;
	let a5;
	let img6;
	let img6_src_value;
	let t7;
	let div3;
	let t8;
	let div5;
	let div6_intro;
	let div6_outro;
	let current;
	let mounted;
	let dispose;
	let each_value_1 = /*links*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	return {
		c() {
			div6 = element("div");
			div0 = element("div");
			button = element("button");
			img0 = element("img");
			t0 = space();
			div4 = element("div");
			div1 = element("div");
			a0 = element("a");
			img1 = element("img");
			t1 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t2 = space();
			div2 = element("div");
			a1 = element("a");
			img2 = element("img");
			t3 = space();
			a2 = element("a");
			img3 = element("img");
			t4 = space();
			a3 = element("a");
			img4 = element("img");
			t5 = space();
			a4 = element("a");
			img5 = element("img");
			t6 = space();
			a5 = element("a");
			img6 = element("img");
			t7 = space();
			div3 = element("div");
			t8 = space();
			div5 = element("div");
			this.h();
		},
		l(nodes) {
			div6 = claim_element(nodes, "DIV", { class: true });
			var div6_nodes = children(div6);
			div0 = claim_element(div6_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			button = claim_element(div0_nodes, "BUTTON", { class: true });
			var button_nodes = children(button);
			img0 = claim_element(button_nodes, "IMG", { alt: true, src: true, class: true });
			button_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t0 = claim_space(div6_nodes);
			div4 = claim_element(div6_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			div1 = claim_element(div4_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a0 = claim_element(div1_nodes, "A", { href: true, class: true });
			var a0_nodes = children(a0);
			img1 = claim_element(a0_nodes, "IMG", { src: true, alt: true, class: true });
			a0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t1 = claim_space(div4_nodes);
			ul = claim_element(div4_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			t2 = claim_space(div4_nodes);
			div2 = claim_element(div4_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			a1 = claim_element(div2_nodes, "A", { rel: true, href: true, class: true });
			var a1_nodes = children(a1);
			img2 = claim_element(a1_nodes, "IMG", { alt: true, src: true, class: true });
			a1_nodes.forEach(detach);
			t3 = claim_space(div2_nodes);

			a2 = claim_element(div2_nodes, "A", {
				target: true,
				rel: true,
				href: true,
				class: true
			});

			var a2_nodes = children(a2);
			img3 = claim_element(a2_nodes, "IMG", { alt: true, src: true, class: true });
			a2_nodes.forEach(detach);
			t4 = claim_space(div2_nodes);

			a3 = claim_element(div2_nodes, "A", {
				target: true,
				rel: true,
				href: true,
				class: true
			});

			var a3_nodes = children(a3);
			img4 = claim_element(a3_nodes, "IMG", { alt: true, src: true, class: true });
			a3_nodes.forEach(detach);
			t5 = claim_space(div2_nodes);

			a4 = claim_element(div2_nodes, "A", {
				target: true,
				rel: true,
				href: true,
				class: true
			});

			var a4_nodes = children(a4);
			img5 = claim_element(a4_nodes, "IMG", { alt: true, src: true, class: true });
			a4_nodes.forEach(detach);
			t6 = claim_space(div2_nodes);

			a5 = claim_element(div2_nodes, "A", {
				target: true,
				rel: true,
				href: true,
				class: true
			});

			var a5_nodes = children(a5);
			img6 = claim_element(a5_nodes, "IMG", { alt: true, src: true, class: true });
			a5_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t7 = claim_space(div4_nodes);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			t8 = claim_space(div6_nodes);
			div5 = claim_element(div6_nodes, "DIV", { class: true });
			children(div5).forEach(detach);
			div6_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(img0, "alt", "burger icon");
			if (!src_url_equal(img0.src, img0_src_value = "https://cdn.skystudio.uz.ua/old/icons/cross.svg")) attr(img0, "src", img0_src_value);
			attr(img0, "class", "svelte-u4p3nq");
			attr(button, "class", "svelte-u4p3nq");
			attr(div0, "class", "cross svelte-u4p3nq");
			if (!src_url_equal(img1.src, img1_src_value = "https://cdn.skystudio.uz.ua/old/skystudio_logo.svg")) attr(img1, "src", img1_src_value);
			attr(img1, "alt", "Logo SkyStudio");
			attr(img1, "class", "svelte-u4p3nq");
			attr(a0, "href", "/");
			attr(a0, "class", "svelte-u4p3nq");
			attr(div1, "class", "logo svelte-u4p3nq");
			attr(ul, "class", "svelte-u4p3nq");
			attr(img2, "alt", "fb icon");
			if (!src_url_equal(img2.src, img2_src_value = "https://cdn.skystudio.uz.ua/old/icons/phone.svg")) attr(img2, "src", img2_src_value);
			attr(img2, "class", "svelte-u4p3nq");
			attr(a1, "rel", "noreferrer");
			attr(a1, "href", "tel:+380950889787");
			attr(a1, "class", "svelte-u4p3nq");
			attr(img3, "alt", "instagram icon");
			if (!src_url_equal(img3.src, img3_src_value = "https://cdn.skystudio.uz.ua/old/icons/insta.svg")) attr(img3, "src", img3_src_value);
			attr(img3, "class", "svelte-u4p3nq");
			set_style(img3, "--size", `1.7rem`);
			attr(a2, "target", "_blank");
			attr(a2, "rel", "noreferrer");
			attr(a2, "href", "https://www.instagram.com/sky_studio_uzh/");
			attr(a2, "class", "svelte-u4p3nq");
			attr(img4, "alt", "fb icon");
			if (!src_url_equal(img4.src, img4_src_value = "https://cdn.skystudio.uz.ua/old/icons/fb.svg")) attr(img4, "src", img4_src_value);
			attr(img4, "class", "svelte-u4p3nq");
			attr(a3, "target", "_blank");
			attr(a3, "rel", "noreferrer");
			attr(a3, "href", "https://www.facebook.com/skystudio.uz");
			attr(a3, "class", "svelte-u4p3nq");
			attr(img5, "alt", "telegram icon");
			if (!src_url_equal(img5.src, img5_src_value = "https://cdn.skystudio.uz.ua/old/icons/telegram.svg")) attr(img5, "src", img5_src_value);
			attr(img5, "class", "svelte-u4p3nq");
			set_style(img5, "--size", `1.4rem`);
			attr(a4, "target", "_blank");
			attr(a4, "rel", "noreferrer");
			attr(a4, "href", "https://t.me/macwings");
			attr(a4, "class", "svelte-u4p3nq");
			attr(img6, "alt", "youtube icon");
			if (!src_url_equal(img6.src, img6_src_value = "https://cdn.skystudio.uz.ua/old/icons/youtube.svg")) attr(img6, "src", img6_src_value);
			attr(img6, "class", "svelte-u4p3nq");
			set_style(img6, "--size", `1.4rem`);
			attr(a5, "target", "_blank");
			attr(a5, "rel", "noreferrer");
			attr(a5, "href", "https://youtube.com/@sky_studio_uzh");
			attr(a5, "class", "svelte-u4p3nq");
			attr(div2, "class", "social svelte-u4p3nq");
			attr(div3, "class", "phone svelte-u4p3nq");
			attr(div4, "class", "main svelte-u4p3nq");
			attr(div5, "class", "footer svelte-u4p3nq");
			attr(div6, "class", "mobileMenu svelte-u4p3nq");
		},
		m(target, anchor) {
			insert_hydration(target, div6, anchor);
			append_hydration(div6, div0);
			append_hydration(div0, button);
			append_hydration(button, img0);
			append_hydration(div6, t0);
			append_hydration(div6, div4);
			append_hydration(div4, div1);
			append_hydration(div1, a0);
			append_hydration(a0, img1);
			append_hydration(div4, t1);
			append_hydration(div4, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			append_hydration(div4, t2);
			append_hydration(div4, div2);
			append_hydration(div2, a1);
			append_hydration(a1, img2);
			append_hydration(div2, t3);
			append_hydration(div2, a2);
			append_hydration(a2, img3);
			append_hydration(div2, t4);
			append_hydration(div2, a3);
			append_hydration(a3, img4);
			append_hydration(div2, t5);
			append_hydration(div2, a4);
			append_hydration(a4, img5);
			append_hydration(div2, t6);
			append_hydration(div2, a5);
			append_hydration(a5, img6);
			append_hydration(div4, t7);
			append_hydration(div4, div3);
			append_hydration(div6, t8);
			append_hydration(div6, div5);
			current = true;

			if (!mounted) {
				dispose = [
					listen(button, "click", /*click_handler*/ ctx[8]),
					action_destroyer(/*swipeToClose*/ ctx[4].call(null, div6)),
					listen(div6, "swiperight", /*swiperight_handler*/ ctx[9])
				];

				mounted = true;
			}
		},
		p(new_ctx, dirty) {
			ctx = new_ctx;

			if (dirty & /*checkCurrent, links*/ 9) {
				each_value_1 = /*links*/ ctx[0];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(ul, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}
		},
		i(local) {
			if (current) return;

			add_render_callback(() => {
				if (!current) return;
				if (div6_outro) div6_outro.end(1);

				div6_intro = create_in_transition(div6, fly, {
					easing: circOut,
					y: -200,
					opacity: 1,
					duration: 150
				});

				div6_intro.start();
			});

			current = true;
		},
		o(local) {
			if (div6_intro) div6_intro.invalidate();
			div6_outro = create_out_transition(div6, fly, { easing: circIn, y: -200, duration: 100 });
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div6);
			destroy_each(each_blocks, detaching);
			if (detaching && div6_outro) div6_outro.end();
			mounted = false;
			run_all(dispose);
		}
	};
}

// (372:7) {#each links as {item}
function create_each_block_1(ctx) {
	let li;
	let a;
	let t_value = /*item*/ ctx[12].label + "";
	let t;
	let a_aria_current_value;
	let a_href_value;
	let a_title_value;

	return {
		c() {
			li = element("li");
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);

			a = claim_element(li_nodes, "A", {
				"aria-current": true,
				href: true,
				title: true,
				class: true
			});

			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "aria-current", a_aria_current_value = /*checkCurrent*/ ctx[3](/*item*/ ctx[12].url));
			attr(a, "href", a_href_value = /*item*/ ctx[12].url);
			attr(a, "title", a_title_value = /*item*/ ctx[12].label);
			attr(a, "class", "svelte-u4p3nq");
			toggle_class(a, "current", /*checkCurrent*/ ctx[3](/*item*/ ctx[12].url));
			attr(li, "class", "svelte-u4p3nq");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, a);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*links*/ 1 && t_value !== (t_value = /*item*/ ctx[12].label + "")) set_data(t, t_value);

			if (dirty & /*links*/ 1 && a_aria_current_value !== (a_aria_current_value = /*checkCurrent*/ ctx[3](/*item*/ ctx[12].url))) {
				attr(a, "aria-current", a_aria_current_value);
			}

			if (dirty & /*links*/ 1 && a_href_value !== (a_href_value = /*item*/ ctx[12].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*links*/ 1 && a_title_value !== (a_title_value = /*item*/ ctx[12].label)) {
				attr(a, "title", a_title_value);
			}

			if (dirty & /*checkCurrent, links*/ 9) {
				toggle_class(a, "current", /*checkCurrent*/ ctx[3](/*item*/ ctx[12].url));
			}
		},
		d(detaching) {
			if (detaching) detach(li);
		}
	};
}

// (415:4) {:else}
function create_else_block(ctx) {
	let img;
	let img_src_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = "https://cdn.skystudio.uz.ua/old/skystudio_logo.svg")) attr(img, "src", img_src_value);
			attr(img, "alt", "Logo SkyStudio");
			attr(img, "class", "svelte-u4p3nq");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (409:4) {#if scrollY > scrollTrigger}
function create_if_block(ctx) {
	let img;
	let img_src_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = "https://cdn.skystudio.uz.ua/old/skystudio_logo_scrolled.svg")) attr(img, "src", img_src_value);
			attr(img, "alt", "Logo SkyStudio");
			attr(img, "class", "svelte-u4p3nq");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (421:13) {#each links as {item}
function create_each_block(ctx) {
	let a;
	let t_value = /*item*/ ctx[12].label + "";
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
			a = claim_element(nodes, "A", { href: true, title: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*item*/ ctx[12].url);
			attr(a, "title", a_title_value = /*item*/ ctx[12].label);
			attr(a, "class", "svelte-u4p3nq");
			toggle_class(a, "current", /*checkCurrent*/ ctx[3](/*item*/ ctx[12].url));
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*links*/ 1 && t_value !== (t_value = /*item*/ ctx[12].label + "")) set_data(t, t_value);

			if (dirty & /*links*/ 1 && a_href_value !== (a_href_value = /*item*/ ctx[12].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*links*/ 1 && a_title_value !== (a_title_value = /*item*/ ctx[12].label)) {
				attr(a, "title", a_title_value);
			}

			if (dirty & /*checkCurrent, links*/ 9) {
				toggle_class(a, "current", /*checkCurrent*/ ctx[3](/*item*/ ctx[12].url));
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment(ctx) {
	let scrolling = false;

	let clear_scrolling = () => {
		scrolling = false;
	};

	let scrolling_timeout;
	let t0;
	let header;
	let div5;
	let div0;
	let a0;
	let t1;
	let div1;
	let t2;
	let div2;
	let a1;
	let img0;
	let img0_src_value;
	let t3;
	let a2;
	let img1;
	let img1_src_value;
	let t4;
	let a3;
	let img2;
	let img2_src_value;
	let t5;
	let a4;
	let img3;
	let img3_src_value;
	let t6;
	let div3;
	let t7;
	let div4;
	let button;
	let img4;
	let img4_src_value;
	let current;
	let mounted;
	let dispose;
	add_render_callback(/*onwindowscroll*/ ctx[7]);
	let if_block0 = /*openMenu*/ ctx[2] && create_if_block_1(ctx);

	function select_block_type(ctx, dirty) {
		if (/*scrollY*/ ctx[1] > scrollTrigger) return create_if_block;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block1 = current_block_type(ctx);
	let each_value = /*links*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	return {
		c() {
			if (if_block0) if_block0.c();
			t0 = space();
			header = element("header");
			div5 = element("div");
			div0 = element("div");
			a0 = element("a");
			if_block1.c();
			t1 = space();
			div1 = element("div");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t2 = space();
			div2 = element("div");
			a1 = element("a");
			img0 = element("img");
			t3 = space();
			a2 = element("a");
			img1 = element("img");
			t4 = space();
			a3 = element("a");
			img2 = element("img");
			t5 = space();
			a4 = element("a");
			img3 = element("img");
			t6 = space();
			div3 = element("div");
			t7 = space();
			div4 = element("div");
			button = element("button");
			img4 = element("img");
			this.h();
		},
		l(nodes) {
			if (if_block0) if_block0.l(nodes);
			t0 = claim_space(nodes);
			header = claim_element(nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div5 = claim_element(header_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			div0 = claim_element(div5_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			a0 = claim_element(div0_nodes, "A", { href: true, class: true });
			var a0_nodes = children(a0);
			if_block1.l(a0_nodes);
			a0_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t1 = claim_space(div5_nodes);
			div1 = claim_element(div5_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(div1_nodes);
			}

			div1_nodes.forEach(detach);
			t2 = claim_space(div5_nodes);
			div2 = claim_element(div5_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			a1 = claim_element(div2_nodes, "A", { rel: true, href: true, class: true });
			var a1_nodes = children(a1);
			img0 = claim_element(a1_nodes, "IMG", { alt: true, src: true, class: true });
			a1_nodes.forEach(detach);
			t3 = claim_space(div2_nodes);

			a2 = claim_element(div2_nodes, "A", {
				target: true,
				rel: true,
				href: true,
				class: true
			});

			var a2_nodes = children(a2);
			img1 = claim_element(a2_nodes, "IMG", { alt: true, src: true, class: true });
			a2_nodes.forEach(detach);
			t4 = claim_space(div2_nodes);

			a3 = claim_element(div2_nodes, "A", {
				target: true,
				rel: true,
				href: true,
				class: true
			});

			var a3_nodes = children(a3);
			img2 = claim_element(a3_nodes, "IMG", { alt: true, src: true, class: true });
			a3_nodes.forEach(detach);
			t5 = claim_space(div2_nodes);

			a4 = claim_element(div2_nodes, "A", {
				target: true,
				rel: true,
				href: true,
				class: true
			});

			var a4_nodes = children(a4);
			img3 = claim_element(a4_nodes, "IMG", { alt: true, src: true, class: true });
			a4_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t6 = claim_space(div5_nodes);
			div3 = claim_element(div5_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			div3_nodes.forEach(detach);
			t7 = claim_space(div5_nodes);
			div4 = claim_element(div5_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			button = claim_element(div4_nodes, "BUTTON", { class: true });
			var button_nodes = children(button);
			img4 = claim_element(button_nodes, "IMG", { alt: true, src: true, class: true });
			button_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			header_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a0, "href", "/");
			attr(a0, "class", "svelte-u4p3nq");
			attr(div0, "class", "logo svelte-u4p3nq");
			attr(div1, "class", "nav svelte-u4p3nq");
			attr(img0, "alt", "fb icon");
			if (!src_url_equal(img0.src, img0_src_value = "https://cdn.skystudio.uz.ua/old/icons/phone.svg")) attr(img0, "src", img0_src_value);
			attr(img0, "class", "svelte-u4p3nq");
			attr(a1, "rel", "noreferrer");
			attr(a1, "href", "tel:+380950889787");
			attr(a1, "class", "svelte-u4p3nq");
			attr(img1, "alt", "instagram icon");
			if (!src_url_equal(img1.src, img1_src_value = "https://cdn.skystudio.uz.ua/old/icons/insta.svg")) attr(img1, "src", img1_src_value);
			attr(img1, "class", "svelte-u4p3nq");
			set_style(img1, "--size", `1.5rem`);
			attr(a2, "target", "_blank");
			attr(a2, "rel", "noreferrer");
			attr(a2, "href", "https://www.instagram.com/sky_studio_uzh/");
			attr(a2, "class", "svelte-u4p3nq");
			attr(img2, "alt", "fb icon");
			if (!src_url_equal(img2.src, img2_src_value = "https://cdn.skystudio.uz.ua/old/icons/fb.svg")) attr(img2, "src", img2_src_value);
			attr(img2, "class", "svelte-u4p3nq");
			attr(a3, "target", "_blank");
			attr(a3, "rel", "noreferrer");
			attr(a3, "href", "https://www.facebook.com/skystudio.uz");
			attr(a3, "class", "svelte-u4p3nq");
			attr(img3, "alt", "youtube icon");
			if (!src_url_equal(img3.src, img3_src_value = "https://cdn.skystudio.uz.ua/old/icons/youtube.svg")) attr(img3, "src", img3_src_value);
			attr(img3, "class", "svelte-u4p3nq");
			attr(a4, "target", "_blank");
			attr(a4, "rel", "noreferrer");
			attr(a4, "href", "https://youtube.com/@sky_studio_uzh");
			attr(a4, "class", "svelte-u4p3nq");
			attr(div2, "class", "social svelte-u4p3nq");
			attr(div3, "class", "langs");
			attr(img4, "alt", "burger icon");
			if (!src_url_equal(img4.src, img4_src_value = "https://cdn.skystudio.uz.ua/old/icons/hamburger.svg")) attr(img4, "src", img4_src_value);
			attr(img4, "class", "svelte-u4p3nq");
			attr(button, "class", "svelte-u4p3nq");
			attr(div4, "class", "burger svelte-u4p3nq");
			attr(div5, "class", "container svelte-u4p3nq");
			attr(header, "class", "svelte-u4p3nq");
			toggle_class(header, "scrolled", /*scrollY*/ ctx[1] > scrollTrigger);
		},
		m(target, anchor) {
			if (if_block0) if_block0.m(target, anchor);
			insert_hydration(target, t0, anchor);
			insert_hydration(target, header, anchor);
			append_hydration(header, div5);
			append_hydration(div5, div0);
			append_hydration(div0, a0);
			if_block1.m(a0, null);
			append_hydration(div5, t1);
			append_hydration(div5, div1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(div1, null);
				}
			}

			append_hydration(div5, t2);
			append_hydration(div5, div2);
			append_hydration(div2, a1);
			append_hydration(a1, img0);
			append_hydration(div2, t3);
			append_hydration(div2, a2);
			append_hydration(a2, img1);
			append_hydration(div2, t4);
			append_hydration(div2, a3);
			append_hydration(a3, img2);
			append_hydration(div2, t5);
			append_hydration(div2, a4);
			append_hydration(a4, img3);
			append_hydration(div5, t6);
			append_hydration(div5, div3);
			append_hydration(div5, t7);
			append_hydration(div5, div4);
			append_hydration(div4, button);
			append_hydration(button, img4);
			current = true;

			if (!mounted) {
				dispose = [
					listen(window_1, "scroll", () => {
						scrolling = true;
						clearTimeout(scrolling_timeout);
						scrolling_timeout = setTimeout(clear_scrolling, 100);
						/*onwindowscroll*/ ctx[7]();
					}),
					listen(button, "click", /*click_handler_1*/ ctx[10])
				];

				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*scrollY*/ 2 && !scrolling) {
				scrolling = true;
				clearTimeout(scrolling_timeout);
				scrollTo(window_1.pageXOffset, /*scrollY*/ ctx[1]);
				scrolling_timeout = setTimeout(clear_scrolling, 100);
			}

			if (/*openMenu*/ ctx[2]) {
				if (if_block0) {
					if_block0.p(ctx, dirty);

					if (dirty & /*openMenu*/ 4) {
						transition_in(if_block0, 1);
					}
				} else {
					if_block0 = create_if_block_1(ctx);
					if_block0.c();
					transition_in(if_block0, 1);
					if_block0.m(t0.parentNode, t0);
				}
			} else if (if_block0) {
				group_outros();

				transition_out(if_block0, 1, 1, () => {
					if_block0 = null;
				});

				check_outros();
			}

			if (current_block_type !== (current_block_type = select_block_type(ctx))) {
				if_block1.d(1);
				if_block1 = current_block_type(ctx);

				if (if_block1) {
					if_block1.c();
					if_block1.m(a0, null);
				}
			}

			if (dirty & /*links, checkCurrent*/ 9) {
				each_value = /*links*/ ctx[0];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(div1, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if (!current || dirty & /*scrollY, scrollTrigger*/ 2) {
				toggle_class(header, "scrolled", /*scrollY*/ ctx[1] > scrollTrigger);
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block0);
			current = true;
		},
		o(local) {
			transition_out(if_block0);
			current = false;
		},
		d(detaching) {
			if (if_block0) if_block0.d(detaching);
			if (detaching) detach(t0);
			if (detaching) detach(header);
			if_block1.d();
			destroy_each(each_blocks, detaching);
			mounted = false;
			run_all(dispose);
		}
	};
}

const scrollTrigger = 200;

function instance($$self, $$props, $$invalidate) {
	let { props } = $$props;
	let { links } = $$props;
	let scrollY = 0;
	let openMenu = false;
	const current_url = page ? new URL(page.baseURI) : window.location;

	function checkCurrent(item_url) {
		const current = current_url.pathname.split("/").slice(-1).pop();
		console.log(current, item_url);
		if (item_url === `/${current === 'index' ? '' : current}`) return true;
		return false;
	}

	const swipeToClose = node => {
		let touchStart, touchEnd;
		let touchVerticalStart, touchVerticalEnd;

		function handleTouchStart(e) {
			touchStart = e.targetTouches[0].clientX;
			touchVerticalStart = e.targetTouches[0].clientY;
		}

		function handleTouchEnd(e) {
			if (touchEnd - touchStart > 100 && Math.abs(touchVerticalEnd - touchVerticalStart) < 100) {
				node.dispatchEvent(new CustomEvent('swiperight'));
			}
		}

		function handleTouchMove(e) {
			touchEnd = e.targetTouches[0].clientX;
			touchVerticalEnd = e.targetTouches[0].clientY;
		}

		node.addEventListener('touchstart', handleTouchStart);
		node.addEventListener('touchmove', handleTouchMove);
		node.addEventListener('touchend', handleTouchEnd);

		return {
			destroy() {
				node.removeEventListener('touchstart', handleTouchStart, true);
				node.removeEventListener('touchmove', handleTouchMove, true);
				node.removeEventListener('touchend', handleTouchEnd, true);
			}
		};
	};

	const swipable = (node, { length = 50 }) => {
		let touchStart, touchEnd;
		let touchVerticalStart, touchVerticalEnd;

		function handleTouchStart(e) {
			touchStart = e.targetTouches[0].clientX;
			touchVerticalStart = e.targetTouches[0].clientY;
		}

		function handleTouchEnd(e) {
			if (Math.abs(touchVerticalEnd - touchVerticalStart) < 50) if (touchEnd - touchStart > length) {
				node.dispatchEvent(new CustomEvent('swiperight'));
			} else if (touchStart - touchEnd > length) {
				node.dispatchEvent(new CustomEvent('swipeleft'));
			}
		}

		function handleTouchMove(e) {
			touchEnd = e.targetTouches[0].clientX;
			touchVerticalEnd = e.targetTouches[0].clientY;
		}

		node.addEventListener('touchstart', handleTouchStart);
		node.addEventListener('touchmove', handleTouchMove);
		node.addEventListener('touchend', handleTouchEnd);

		return {
			destroy() {
				node.removeEventListener('touchstart', handleTouchStart, true);
				node.removeEventListener('touchmove', handleTouchMove, true);
				node.removeEventListener('touchend', handleTouchEnd, true);
			}
		};
	};

	function onwindowscroll() {
		$$invalidate(1, scrollY = window_1.pageYOffset);
	}

	const click_handler = () => $$invalidate(2, openMenu = false);
	const swiperight_handler = () => $$invalidate(2, openMenu = false);
	const click_handler_1 = () => $$invalidate(2, openMenu = true);

	$$self.$$set = $$props => {
		if ('props' in $$props) $$invalidate(5, props = $$props.props);
		if ('links' in $$props) $$invalidate(0, links = $$props.links);
	};

	return [
		links,
		scrollY,
		openMenu,
		checkCurrent,
		swipeToClose,
		props,
		swipable,
		onwindowscroll,
		click_handler,
		swiperight_handler,
		click_handler_1
	];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { props: 5, links: 0, swipable: 6 });
	}

	get swipable() {
		return this.$$.ctx[6];
	}
}

export { Component as default };
