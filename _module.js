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
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
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
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
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
/**
 * List of attributes that should always be set through the attr method,
 * because updating them through the property setter doesn't work reliably.
 * In the example of `width`/`height`, the problem is that the setter only
 * accepts numeric values, but the attribute can also be set to a string like `50%`.
 * If this list becomes too big, rethink this approach.
 */
const always_set_through_set_attribute = ['width', 'height'];
function set_attributes(node, attributes) {
    // @ts-ignore
    const descriptors = Object.getOwnPropertyDescriptors(node.__proto__);
    for (const key in attributes) {
        if (attributes[key] == null) {
            node.removeAttribute(key);
        }
        else if (key === 'style') {
            node.style.cssText = attributes[key];
        }
        else if (key === '__value') {
            node.value = node[key] = attributes[key];
        }
        else if (descriptors[key] && descriptors[key].set && always_set_through_set_attribute.indexOf(key) === -1) {
            node[key] = attributes[key];
        }
        else {
            attr(node, key, attributes[key]);
        }
    }
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
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
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
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
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
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
function create_bidirectional_transition(node, fn, params, intro) {
    const options = { direction: 'both' };
    let config = fn(node, params, options);
    let t = intro ? 0 : 1;
    let running_program = null;
    let pending_program = null;
    let animation_name = null;
    function clear_animation() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function init(program, duration) {
        const d = (program.b - t);
        duration *= Math.abs(d);
        return {
            a: t,
            b: program.b,
            d,
            duration,
            start: program.start,
            end: program.start + duration,
            group: program.group
        };
    }
    function go(b) {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        const program = {
            start: now() + delay,
            b
        };
        if (!b) {
            // @ts-ignore todo: improve typings
            program.group = outros;
            outros.r += 1;
        }
        if (running_program || pending_program) {
            pending_program = program;
        }
        else {
            // if this is an intro, and there's a delay, we need to do
            // an initial tick and/or apply CSS animation immediately
            if (css) {
                clear_animation();
                animation_name = create_rule(node, t, b, duration, delay, easing, css);
            }
            if (b)
                tick(0, 1);
            running_program = init(program, duration);
            add_render_callback(() => dispatch(node, b, 'start'));
            loop(now => {
                if (pending_program && now > pending_program.start) {
                    running_program = init(pending_program, duration);
                    pending_program = null;
                    dispatch(node, running_program.b, 'start');
                    if (css) {
                        clear_animation();
                        animation_name = create_rule(node, t, running_program.b, running_program.duration, 0, easing, config.css);
                    }
                }
                if (running_program) {
                    if (now >= running_program.end) {
                        tick(t = running_program.b, 1 - t);
                        dispatch(node, running_program.b, 'end');
                        if (!pending_program) {
                            // we're done
                            if (running_program.b) {
                                // intro — we can tidy up immediately
                                clear_animation();
                            }
                            else {
                                // outro — needs to be coordinated
                                if (!--running_program.group.r)
                                    run_all(running_program.group.c);
                            }
                        }
                        running_program = null;
                    }
                    else if (now >= running_program.start) {
                        const p = now - running_program.start;
                        t = running_program.a + running_program.d * easing(p / running_program.duration);
                        tick(t, 1 - t);
                    }
                }
                return !!(running_program || pending_program);
            });
        }
    }
    return {
        run(b) {
            if (is_function(config)) {
                wait().then(() => {
                    // @ts-ignore
                    config = config(options);
                    go(b);
                });
            }
            else {
                go(b);
            }
        },
        end() {
            clear_animation();
            running_program = pending_program = null;
        }
    };
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
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
			t = text("@font-face {\n  font-family: 'ProximaNova';\n  font-style: normal;\n  font-weight: 300;\n  font-stretch: 100%;\n  font-display: swap;\n  src: url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Regular.woff2) format('woff2'),\n    url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Regular.ttf);\n}\n\n@font-face {\n  font-family: 'ProximaNova';\n  font-style: normal;\n  font-weight: 600;\n  font-stretch: 100%;\n  font-display: swap;\n  src: url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Bold.woff2) format('woff2'),\n    url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Bold.ttf);\n}\n\n@font-face {\n  font-family: 'ProximaNova';\n  font-style: normal;\n  font-weight: 900;\n  font-stretch: 100%;\n  font-display: swap;\n  src: url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Black.woff2) format('woff2'),\n    url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Black.ttf);\n}\n\n@font-face {\n  font-family: 'NotoSerif';\n  font-style: normal;\n  font-weight: 700;\n  font-stretch: 100%;\n  font-display: swap;\n  src: url(https://cdn.skystudio.uz.ua/old/fonts/Noto_Serif/NotoSerif-Regular.ttf);\n}\n\n/* Reset & standardize default styles */\n/*@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;*/\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options\n  --color-accent: #004700;\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 0;\n  --border-color: #e0e1e1;\n  */\n  --color-accent: #FEC93C;\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 0;\n  --border-color: #294c80;\n\n  --darkColor: #294c80;\n  --lightColor: #2d8fc5;\n  --accentColor: #FEC93C;\n  --accentDarkerColor: #FEC93C;\n  --font1: \"ProximaNova\", sans-serif;\n  --font2: \"NotoSerif\", serif;\n\n  --color: #0f0f16;\n  --colorGray: #b6b6d2;\n  --zoom: 0.9;\n}\n\nhtml {\n  /* zoom: var(--zoom); */\n}\n\nhtml,\nbody {}\n\n\n.noscroll {\n  overflow: hidden;\n}\n\n\n\n/* Root element (use instead of `body`) */\n#page {\n  zoom: var(--zoom);\n  scroll-behavior: smooth;\n  scroll-padding: 6em;\n  padding: 0;\n  margin: 0;\n  background-color: var(--darkColor);\n  font-size: 16px;\n\n\n  color: var(--color);\n\n\n  background: white;\n\n  font-size: 16px;\n  font-family: var(--font1);\n  font-weight: 300;\n}\n#page a {\n    text-decoration: none;\n  }\n@media (hover: hover) and (pointer: fine) {\n    #page a:hover {\n      text-decoration: none;\n    }\n  }\n\n/* Elements */\n.section {}\n\n.section-container {\n  max-width: 1200px;\n  margin: 0 auto;\n  width: auto;\n  padding-bottom: 3rem;\n}\n\n@media screen and (min-width: 768px) {\n\n.section-container {\n    width: calc(100% - 2rem)\n}\n  }\n\n.section-container.no-bottom-padding {\n    padding-bottom: 0;\n  }\n\na.link {\n  line-height: 1.3;\n\n  border-bottom: 2px solid var(--color-accent);\n  transform: translateY(-2px);\n  /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: 2.5rem;\n  line-height: 1.15;\n\n}\n\n.button {\n  color: white;\n  background: var(--color-accent, rebeccapurple);\n  border-radius: 0;\n  padding: 18px 24px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0;\n}\n\n/* reset */\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent, rebeccapurple);\n  }\n\n/* Content Section */\n.content {\n  max-width: 900px;\n  margin: 0 auto;\n  padding: 3rem 2rem;\n}\n.content p {\n    margin-bottom: 1rem;\n    line-height: 1.5;\n  }\n.content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n.content a.link {\n    line-height: 1.3;\n    font-weight: 500;\n    border-bottom: 2px solid var(--color-accent);\n    transform: translateY(-2px);\n    /* move link back into place */\n    transition: var(--transition, 0.1s border);\n  }\n.content a.link:hover {\n      border-color: transparent;\n    }\n.content h1 {\n    font-size: 3rem;\n    font-weight: 500;\n    line-height: 1.1;\n    margin-bottom: 1.5rem;\n  }\n.content h2 {\n    font-size: 2.5rem;\n    font-weight: 500;\n    margin-bottom: 1rem;\n  }\n.content h3 {\n    font-size: 2rem;\n    font-weight: 500;\n    margin-bottom: 1rem;\n  }\n.content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.content blockquote {\n    padding: 2rem;\n    margin-top: 1.5rem;\n    margin-bottom: 1.5rem;\n    border-left: 5px solid var(--color-accent);\n  }");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-13vzyi1', document.head);

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
			t = claim_text(style_nodes, "@font-face {\n  font-family: 'ProximaNova';\n  font-style: normal;\n  font-weight: 300;\n  font-stretch: 100%;\n  font-display: swap;\n  src: url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Regular.woff2) format('woff2'),\n    url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Regular.ttf);\n}\n\n@font-face {\n  font-family: 'ProximaNova';\n  font-style: normal;\n  font-weight: 600;\n  font-stretch: 100%;\n  font-display: swap;\n  src: url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Bold.woff2) format('woff2'),\n    url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Bold.ttf);\n}\n\n@font-face {\n  font-family: 'ProximaNova';\n  font-style: normal;\n  font-weight: 900;\n  font-stretch: 100%;\n  font-display: swap;\n  src: url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Black.woff2) format('woff2'),\n    url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Black.ttf);\n}\n\n@font-face {\n  font-family: 'NotoSerif';\n  font-style: normal;\n  font-weight: 700;\n  font-stretch: 100%;\n  font-display: swap;\n  src: url(https://cdn.skystudio.uz.ua/old/fonts/Noto_Serif/NotoSerif-Regular.ttf);\n}\n\n/* Reset & standardize default styles */\n/*@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;*/\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options\n  --color-accent: #004700;\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 0;\n  --border-color: #e0e1e1;\n  */\n  --color-accent: #FEC93C;\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 0;\n  --border-color: #294c80;\n\n  --darkColor: #294c80;\n  --lightColor: #2d8fc5;\n  --accentColor: #FEC93C;\n  --accentDarkerColor: #FEC93C;\n  --font1: \"ProximaNova\", sans-serif;\n  --font2: \"NotoSerif\", serif;\n\n  --color: #0f0f16;\n  --colorGray: #b6b6d2;\n  --zoom: 0.9;\n}\n\nhtml {\n  /* zoom: var(--zoom); */\n}\n\nhtml,\nbody {}\n\n\n.noscroll {\n  overflow: hidden;\n}\n\n\n\n/* Root element (use instead of `body`) */\n#page {\n  zoom: var(--zoom);\n  scroll-behavior: smooth;\n  scroll-padding: 6em;\n  padding: 0;\n  margin: 0;\n  background-color: var(--darkColor);\n  font-size: 16px;\n\n\n  color: var(--color);\n\n\n  background: white;\n\n  font-size: 16px;\n  font-family: var(--font1);\n  font-weight: 300;\n}\n#page a {\n    text-decoration: none;\n  }\n@media (hover: hover) and (pointer: fine) {\n    #page a:hover {\n      text-decoration: none;\n    }\n  }\n\n/* Elements */\n.section {}\n\n.section-container {\n  max-width: 1200px;\n  margin: 0 auto;\n  width: auto;\n  padding-bottom: 3rem;\n}\n\n@media screen and (min-width: 768px) {\n\n.section-container {\n    width: calc(100% - 2rem)\n}\n  }\n\n.section-container.no-bottom-padding {\n    padding-bottom: 0;\n  }\n\na.link {\n  line-height: 1.3;\n\n  border-bottom: 2px solid var(--color-accent);\n  transform: translateY(-2px);\n  /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: 2.5rem;\n  line-height: 1.15;\n\n}\n\n.button {\n  color: white;\n  background: var(--color-accent, rebeccapurple);\n  border-radius: 0;\n  padding: 18px 24px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0;\n}\n\n/* reset */\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent, rebeccapurple);\n  }\n\n/* Content Section */\n.content {\n  max-width: 900px;\n  margin: 0 auto;\n  padding: 3rem 2rem;\n}\n.content p {\n    margin-bottom: 1rem;\n    line-height: 1.5;\n  }\n.content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n.content a.link {\n    line-height: 1.3;\n    font-weight: 500;\n    border-bottom: 2px solid var(--color-accent);\n    transform: translateY(-2px);\n    /* move link back into place */\n    transition: var(--transition, 0.1s border);\n  }\n.content a.link:hover {\n      border-color: transparent;\n    }\n.content h1 {\n    font-size: 3rem;\n    font-weight: 500;\n    line-height: 1.1;\n    margin-bottom: 1.5rem;\n  }\n.content h2 {\n    font-size: 2.5rem;\n    font-weight: 500;\n    margin-bottom: 1rem;\n  }\n.content h3 {\n    font-size: 2rem;\n    font-weight: 500;\n    margin-bottom: 1rem;\n  }\n.content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.content blockquote {\n    padding: 2rem;\n    margin-top: 1.5rem;\n    margin-bottom: 1.5rem;\n    border-left: 5px solid var(--color-accent);\n  }");
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

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}

const matchIconName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIconName(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIconName(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIconName(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIconName = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!((icon.provider === "" || icon.provider.match(matchIconName)) && (allowSimpleName && icon.prefix === "" || icon.prefix.match(matchIconName)) && icon.name.match(matchIconName));
};
const defaultIconDimensions = Object.freeze({
  left: 0,
  top: 0,
  width: 16,
  height: 16
});
const defaultIconTransformations = Object.freeze({
  rotate: 0,
  vFlip: false,
  hFlip: false
});
const defaultIconProps = Object.freeze({
  ...defaultIconDimensions,
  ...defaultIconTransformations
});
const defaultExtendedIconProps = Object.freeze({
  ...defaultIconProps,
  body: "",
  hidden: false
});
function mergeIconTransformations(obj1, obj2) {
  const result = {};
  if (!obj1.hFlip !== !obj2.hFlip) {
    result.hFlip = true;
  }
  if (!obj1.vFlip !== !obj2.vFlip) {
    result.vFlip = true;
  }
  const rotate = ((obj1.rotate || 0) + (obj2.rotate || 0)) % 4;
  if (rotate) {
    result.rotate = rotate;
  }
  return result;
}
function mergeIconData(parent, child) {
  const result = mergeIconTransformations(parent, child);
  for (const key in defaultExtendedIconProps) {
    if (key in defaultIconTransformations) {
      if (key in parent && !(key in result)) {
        result[key] = defaultIconTransformations[key];
      }
    } else if (key in child) {
      result[key] = child[key];
    } else if (key in parent) {
      result[key] = parent[key];
    }
  }
  return result;
}
function getIconsTree(data, names) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  const resolved = /* @__PURE__ */ Object.create(null);
  function resolve(name) {
    if (icons[name]) {
      return resolved[name] = [];
    }
    if (!(name in resolved)) {
      resolved[name] = null;
      const parent = aliases[name] && aliases[name].parent;
      const value = parent && resolve(parent);
      if (value) {
        resolved[name] = [parent].concat(value);
      }
    }
    return resolved[name];
  }
  (names || Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}
function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(icons[name2] || aliases[name2], currentProps);
  }
  parse(name);
  tree.forEach(parse);
  return mergeIconData(data, currentProps);
}
function parseIconSet(data, callback) {
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const tree = getIconsTree(data);
  for (const name in tree) {
    const item = tree[name];
    if (item) {
      callback(name, internalGetIconData(data, name, item));
      names.push(name);
    }
  }
  return names;
}
const optionalPropertyDefaults = {
  provider: "",
  aliases: {},
  not_found: {},
  ...defaultIconDimensions
};
function checkOptionalProps(item, defaults) {
  for (const prop in defaults) {
    if (prop in item && typeof item[prop] !== typeof defaults[prop]) {
      return false;
    }
  }
  return true;
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  if (!checkOptionalProps(obj, optionalPropertyDefaults)) {
    return null;
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  return data;
}
const dataStorage = /* @__PURE__ */ Object.create(null);
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ new Set()
  };
}
function getStorage(provider, prefix) {
  const providerStorage = dataStorage[provider] || (dataStorage[provider] = /* @__PURE__ */ Object.create(null));
  return providerStorage[prefix] || (providerStorage[prefix] = newStorage(provider, prefix));
}
function addIconSet(storage2, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage2.icons[name] = icon;
    } else {
      storage2.missing.add(name);
    }
  });
}
function addIconToStorage(storage2, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage2.icons[name] = {...icon};
      return true;
    }
  } catch (err) {
  }
  return false;
}
let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  if (icon) {
    const storage2 = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage2.icons[iconName] || (storage2.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage2 = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage2, icon.name, data);
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = data.provider || "";
  }
  if (simpleNames && !provider && !data.prefix) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (icon && addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  const prefix = data.prefix;
  if (!validateIconName({
    provider,
    prefix,
    name: "a"
  })) {
    return false;
  }
  const storage2 = getStorage(provider, prefix);
  return !!addIconSet(storage2, data);
}
const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  ...defaultIconSizeCustomisations,
  ...defaultIconTransformations
});
const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision || 100;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}
const isUnsetKeyword = (value) => value === "unset" || value === "undefined" || value === "none";
function iconToSVG(icon, customisations) {
  const fullIcon = {
    ...defaultIconProps,
    ...icon
  };
  const fullCustomisations = {
    ...defaultIconCustomisations,
    ...customisations
  };
  const box = {
    left: fullIcon.left,
    top: fullIcon.top,
    width: fullIcon.width,
    height: fullIcon.height
  };
  let body = fullIcon.body;
  [fullIcon, fullCustomisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push("translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")");
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push("translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")");
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift("rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
      case 2:
        transformations.unshift("rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")");
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift("rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== box.top) {
        tempValue = box.left;
        box.left = box.top;
        box.top = tempValue;
      }
      if (box.width !== box.height) {
        tempValue = box.width;
        box.width = box.height;
        box.height = tempValue;
      }
    }
    if (transformations.length) {
      body = '<g transform="' + transformations.join(" ") + '">' + body + "</g>";
    }
  });
  const customisationsWidth = fullCustomisations.width;
  const customisationsHeight = fullCustomisations.height;
  const boxWidth = box.width;
  const boxHeight = box.height;
  let width;
  let height;
  if (customisationsWidth === null) {
    height = customisationsHeight === null ? "1em" : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
    width = calculateSize(height, boxWidth / boxHeight);
  } else {
    width = customisationsWidth === "auto" ? boxWidth : customisationsWidth;
    height = customisationsHeight === null ? calculateSize(width, boxHeight / boxWidth) : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
  }
  const attributes = {};
  const setAttr = (prop, value) => {
    if (!isUnsetKeyword(value)) {
      attributes[prop] = value.toString();
    }
  };
  setAttr("width", width);
  setAttr("height", height);
  attributes.viewBox = box.left.toString() + " " + box.top.toString() + " " + boxWidth.toString() + " " + boxHeight.toString();
  return {
    attributes,
    body
  };
}
const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  const suffix = "suffix" + (Math.random() * 16777216 | Date.now()).toString(16);
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"), "$1" + newID + suffix + "$3");
  });
  body = body.replace(new RegExp(suffix, "g"), "");
  return body;
}
const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}
function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    resources,
    path: source.path || "/",
    maxURL: source.maxURL || 500,
    rotate: source.rotate || 750,
    timeout: source.timeout || 5e3,
    random: source.random === true,
    index: source.index || 0,
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}
const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
};
let fetchModule = detectFetch();
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = prefix + ".json?icons=";
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  const maxLength = calculateMaxLength(provider, prefix);
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    const config = getAPIConfig(provider);
    if (config) {
      return config.path;
    }
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      const urlParams = new URLSearchParams({
        icons: iconsList
      });
      path += prefix + ".json?" + urlParams.toString();
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        if (data === 404) {
          callback("abort", data);
        } else {
          callback("next", defaultError);
        }
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};
function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage2 = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const providerStorage = storage2[provider] || (storage2[provider] = /* @__PURE__ */ Object.create(null));
    const localStorage = providerStorage[prefix] || (providerStorage[prefix] = getStorage(provider, prefix));
    let list;
    if (name in localStorage.icons) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing.has(name)) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}
function removeCallback(storages, id) {
  storages.forEach((storage2) => {
    const items = storage2.loaderCallbacks;
    if (items) {
      storage2.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage2) {
  if (!storage2.pendingCallbacksFlag) {
    storage2.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage2.pendingCallbacksFlag = false;
      const items = storage2.loaderCallbacks ? storage2.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage2.provider;
      const prefix = storage2.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage2.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage2.missing.has(name)) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([storage2], item.id);
          }
          item.callback(icons.loaded.slice(0), icons.missing.slice(0), icons.pending.slice(0), item.abort);
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((storage2) => {
    (storage2.loaderCallbacks || (storage2.loaderCallbacks = [])).push(item);
  });
  return abort;
}
function listToIcons(list, validate = true, simpleNames2 = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames2) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}
function initRedundancy(cfg) {
  const config = {
    ...defaultConfig,
    ...cfg
  };
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(config, payload, queryCallback, (data, error) => {
      cleanup();
      if (doneCallback) {
        doneCallback(data, error);
      }
    });
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    return queries.find((value) => {
      return callback(value);
    }) || null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}
function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (!redundancyCache[provider]) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send2;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send2 = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send2 = api.send;
      }
    }
  }
  if (!redundancy || !send2) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send2, callback)().abort;
}
const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
function getStoredItem(func, key) {
  try {
    return func.getItem(key);
  } catch (err) {
  }
}
function setStoredItem(func, key, value) {
  try {
    func.setItem(key, value);
    return true;
  } catch (err) {
  }
}
function removeStoredItem(func, key) {
  try {
    func.removeItem(key);
  } catch (err) {
  }
}
function setBrowserStorageItemsCount(storage2, value) {
  return setStoredItem(storage2, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage2) {
  return parseInt(getStoredItem(storage2, browserCacheCountKey)) || 0;
}
const browserStorageConfig = {
  local: true,
  session: true
};
const browserStorageEmptyItems = {
  local: /* @__PURE__ */ new Set(),
  session: /* @__PURE__ */ new Set()
};
let browserStorageStatus = false;
function setBrowserStorageStatus(status) {
  browserStorageStatus = status;
}
let _window = typeof window === "undefined" ? {} : window;
function getBrowserStorage(key) {
  const attr = key + "Storage";
  try {
    if (_window && _window[attr] && typeof _window[attr].length === "number") {
      return _window[attr];
    }
  } catch (err) {
  }
  browserStorageConfig[key] = false;
}
function iterateBrowserStorage(key, callback) {
  const func = getBrowserStorage(key);
  if (!func) {
    return;
  }
  const version = getStoredItem(func, browserCacheVersionKey);
  if (version !== browserCacheVersion) {
    if (version) {
      const total2 = getBrowserStorageItemsCount(func);
      for (let i = 0; i < total2; i++) {
        removeStoredItem(func, browserCachePrefix + i.toString());
      }
    }
    setStoredItem(func, browserCacheVersionKey, browserCacheVersion);
    setBrowserStorageItemsCount(func, 0);
    return;
  }
  const minTime = Math.floor(Date.now() / browserStorageHour) - browserStorageCacheExpiration;
  const parseItem = (index) => {
    const name = browserCachePrefix + index.toString();
    const item = getStoredItem(func, name);
    if (typeof item !== "string") {
      return;
    }
    try {
      const data = JSON.parse(item);
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && callback(data, index)) {
        return true;
      }
    } catch (err) {
    }
    removeStoredItem(func, name);
  };
  let total = getBrowserStorageItemsCount(func);
  for (let i = total - 1; i >= 0; i--) {
    if (!parseItem(i)) {
      if (i === total - 1) {
        total--;
        setBrowserStorageItemsCount(func, total);
      } else {
        browserStorageEmptyItems[key].add(i);
      }
    }
  }
}
function initBrowserStorage() {
  if (browserStorageStatus) {
    return;
  }
  setBrowserStorageStatus(true);
  for (const key in browserStorageConfig) {
    iterateBrowserStorage(key, (item) => {
      const iconSet = item.data;
      const provider = item.provider;
      const prefix = iconSet.prefix;
      const storage2 = getStorage(provider, prefix);
      if (!addIconSet(storage2, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage2.lastModifiedCached = storage2.lastModifiedCached ? Math.min(storage2.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}
function updateLastModified(storage2, lastModified) {
  const lastValue = storage2.lastModifiedCached;
  if (lastValue && lastValue >= lastModified) {
    return lastValue === lastModified;
  }
  storage2.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage2.provider || iconSet.prefix !== storage2.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage2, data) {
  if (!browserStorageStatus) {
    initBrowserStorage();
  }
  function store(key) {
    let func;
    if (!browserStorageConfig[key] || !(func = getBrowserStorage(key))) {
      return;
    }
    const set = browserStorageEmptyItems[key];
    let index;
    if (set.size) {
      set.delete(index = Array.from(set).shift());
    } else {
      index = getBrowserStorageItemsCount(func);
      if (!setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage2.provider,
      data
    };
    return setStoredItem(func, browserCachePrefix + index.toString(), JSON.stringify(item));
  }
  if (data.lastModified && !updateLastModified(storage2, data.lastModified)) {
    return;
  }
  if (!Object.keys(data.icons).length) {
    return;
  }
  if (data.not_found) {
    data = Object.assign({}, data);
    delete data.not_found;
  }
  if (!store("local")) {
    store("session");
  }
}
function emptyCallback() {
}
function loadedNewIcons(storage2) {
  if (!storage2.iconsLoaderFlag) {
    storage2.iconsLoaderFlag = true;
    setTimeout(() => {
      storage2.iconsLoaderFlag = false;
      updateCallbacks(storage2);
    });
  }
}
function loadNewIcons(storage2, icons) {
  if (!storage2.iconsToLoad) {
    storage2.iconsToLoad = icons;
  } else {
    storage2.iconsToLoad = storage2.iconsToLoad.concat(icons).sort();
  }
  if (!storage2.iconsQueueFlag) {
    storage2.iconsQueueFlag = true;
    setTimeout(() => {
      storage2.iconsQueueFlag = false;
      const {provider, prefix} = storage2;
      const icons2 = storage2.iconsToLoad;
      delete storage2.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage2.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(storage2, data);
              if (!parsed.length) {
                return;
              }
              const pending = storage2.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage2, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage2);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(sortedIcons.loaded, sortedIcons.missing, sortedIcons.pending, emptyCallback);
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix} = icon;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push(getStorage(provider, prefix));
    const providerNewIcons = newIcons[provider] || (newIcons[provider] = /* @__PURE__ */ Object.create(null));
    if (!providerNewIcons[prefix]) {
      providerNewIcons[prefix] = [];
    }
  });
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix, name} = icon;
    const storage2 = getStorage(provider, prefix);
    const pendingQueue = storage2.pendingIcons || (storage2.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage2) => {
    const {provider, prefix} = storage2;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage2, newIcons[provider][prefix]);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};
function mergeCustomisations(defaults, item) {
  const result = {
    ...defaults
  };
  for (const key in item) {
    const value = item[key];
    const valueType = typeof value;
    if (key in defaultIconSizeCustomisations) {
      if (value === null || value && (valueType === "string" || valueType === "number")) {
        result[key] = value;
      }
    } else if (valueType === typeof result[key]) {
      result[key] = key === "rotate" ? value % 4 : value;
    }
  }
  return result;
}
const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}
function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
        split = 90;
    }
    if (split) {
      let num = parseFloat(value.slice(0, value.length - units.length));
      if (isNaN(num)) {
        return 0;
      }
      num = num / split;
      return num % 1 === 0 ? cleanup(num) : 0;
    }
  }
  return defaultValue;
}
function iconToHTML(body, attributes) {
  let renderAttribsHTML = body.indexOf("xlink:") === -1 ? "" : ' xmlns:xlink="http://www.w3.org/1999/xlink"';
  for (const attr in attributes) {
    renderAttribsHTML += " " + attr + '="' + attributes[attr] + '"';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg"' + renderAttribsHTML + ">" + body + "</svg>";
}
function encodeSVGforURL(svg) {
  return svg.replace(/"/g, "'").replace(/%/g, "%25").replace(/#/g, "%23").replace(/</g, "%3C").replace(/>/g, "%3E").replace(/\s+/g, " ");
}
function svgToData(svg) {
  return "data:image/svg+xml," + encodeSVGforURL(svg);
}
function svgToURL(svg) {
  return 'url("' + svgToData(svg) + '")';
}
const defaultExtendedIconCustomisations = {
  ...defaultIconCustomisations,
  inline: false
};
const svgDefaults = {
  xmlns: "http://www.w3.org/2000/svg",
  "xmlns:xlink": "http://www.w3.org/1999/xlink",
  "aria-hidden": true,
  role: "img"
};
const commonProps = {
  display: "inline-block"
};
const monotoneProps = {
  "background-color": "currentColor"
};
const coloredProps = {
  "background-color": "transparent"
};
const propsToAdd = {
  image: "var(--svg)",
  repeat: "no-repeat",
  size: "100% 100%"
};
const propsToAddTo = {
  "-webkit-mask": monotoneProps,
  mask: monotoneProps,
  background: coloredProps
};
for (const prefix in propsToAddTo) {
  const list = propsToAddTo[prefix];
  for (const prop in propsToAdd) {
    list[prefix + "-" + prop] = propsToAdd[prop];
  }
}
function fixSize(value) {
  return value + (value.match(/^[-0-9.]+$/) ? "px" : "");
}
function render(icon, props) {
  const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
  const mode = props.mode || "svg";
  const componentProps = mode === "svg" ? {...svgDefaults} : {};
  if (icon.body.indexOf("xlink:") === -1) {
    delete componentProps["xmlns:xlink"];
  }
  let style = typeof props.style === "string" ? props.style : "";
  for (let key in props) {
    const value = props[key];
    if (value === void 0) {
      continue;
    }
    switch (key) {
      case "icon":
      case "style":
      case "onLoad":
      case "mode":
        break;
      case "inline":
      case "hFlip":
      case "vFlip":
        customisations[key] = value === true || value === "true" || value === 1;
        break;
      case "flip":
        if (typeof value === "string") {
          flipFromString(customisations, value);
        }
        break;
      case "color":
        style = style + (style.length > 0 && style.trim().slice(-1) !== ";" ? ";" : "") + "color: " + value + "; ";
        break;
      case "rotate":
        if (typeof value === "string") {
          customisations[key] = rotateFromString(value);
        } else if (typeof value === "number") {
          customisations[key] = value;
        }
        break;
      case "ariaHidden":
      case "aria-hidden":
        if (value !== true && value !== "true") {
          delete componentProps["aria-hidden"];
        }
        break;
      default:
        if (key.slice(0, 3) === "on:") {
          break;
        }
        if (defaultExtendedIconCustomisations[key] === void 0) {
          componentProps[key] = value;
        }
    }
  }
  const item = iconToSVG(icon, customisations);
  const renderAttribs = item.attributes;
  if (customisations.inline) {
    style = "vertical-align: -0.125em; " + style;
  }
  if (mode === "svg") {
    Object.assign(componentProps, renderAttribs);
    if (style !== "") {
      componentProps.style = style;
    }
    let localCounter = 0;
    let id = props.id;
    if (typeof id === "string") {
      id = id.replace(/-/g, "_");
    }
    return {
      svg: true,
      attributes: componentProps,
      body: replaceIDs(item.body, id ? () => id + "ID" + localCounter++ : "iconifySvelte")
    };
  }
  const {body, width, height} = icon;
  const useMask = mode === "mask" || (mode === "bg" ? false : body.indexOf("currentColor") !== -1);
  const html = iconToHTML(body, {
    ...renderAttribs,
    width: width + "",
    height: height + ""
  });
  const url = svgToURL(html);
  const styles = {
    "--svg": url
  };
  const size = (prop) => {
    const value = renderAttribs[prop];
    if (value) {
      styles[prop] = fixSize(value);
    }
  };
  size("width");
  size("height");
  Object.assign(styles, commonProps, useMask ? monotoneProps : coloredProps);
  let customStyle = "";
  for (const key in styles) {
    customStyle += key + ": " + styles[key] + ";";
  }
  componentProps.style = customStyle + style;
  return {
    svg: false,
    attributes: componentProps
  };
}
allowSimpleNames(true);
setAPIModule("", fetchAPIModule);
if (typeof document !== "undefined" && typeof window !== "undefined") {
  initBrowserStorage();
  const _window2 = window;
  if (_window2.IconifyPreload !== void 0) {
    const preload = _window2.IconifyPreload;
    const err = "Invalid IconifyPreload syntax.";
    if (typeof preload === "object" && preload !== null) {
      (preload instanceof Array ? preload : [preload]).forEach((item) => {
        try {
          if (typeof item !== "object" || item === null || item instanceof Array || typeof item.icons !== "object" || typeof item.prefix !== "string" || !addCollection(item)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      });
    }
  }
  if (_window2.IconifyProviders !== void 0) {
    const providers = _window2.IconifyProviders;
    if (typeof providers === "object" && providers !== null) {
      for (let key in providers) {
        const err = "IconifyProviders[" + key + "] is invalid.";
        try {
          const value = providers[key];
          if (typeof value !== "object" || !value || value.resources === void 0) {
            continue;
          }
          if (!addAPIProvider(key, value)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      }
    }
  }
}
function checkIconState(icon, state, mounted, callback, onload) {
  function abortLoading() {
    if (state.loading) {
      state.loading.abort();
      state.loading = null;
    }
  }
  if (typeof icon === "object" && icon !== null && typeof icon.body === "string") {
    state.name = "";
    abortLoading();
    return {data: {...defaultIconProps, ...icon}};
  }
  let iconName;
  if (typeof icon !== "string" || (iconName = stringToIcon(icon, false, true)) === null) {
    abortLoading();
    return null;
  }
  const data = getIconData(iconName);
  if (!data) {
    if (mounted && (!state.loading || state.loading.name !== icon)) {
      abortLoading();
      state.name = "";
      state.loading = {
        name: icon,
        abort: loadIcons([iconName], callback)
      };
    }
    return null;
  }
  abortLoading();
  if (state.name !== icon) {
    state.name = icon;
    if (onload && !state.destroyed) {
      onload(icon);
    }
  }
  const classes = ["iconify"];
  if (iconName.prefix !== "") {
    classes.push("iconify--" + iconName.prefix);
  }
  if (iconName.provider !== "") {
    classes.push("iconify--" + iconName.provider);
  }
  return {data, classes};
}
function generateIcon(icon, props) {
  return icon ? render({
    ...defaultIconProps,
    ...icon
  }, props) : null;
}
var checkIconState_1 = checkIconState;
var generateIcon_1 = generateIcon;

/* generated by Svelte v3.59.1 */

function create_if_block(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

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
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (113:1) {:else}
function create_else_block(ctx) {
	let span;
	let span_levels = [/*data*/ ctx[0].attributes];
	let span_data = {};

	for (let i = 0; i < span_levels.length; i += 1) {
		span_data = assign(span_data, span_levels[i]);
	}

	return {
		c() {
			span = element("span");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			children(span).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(span, span_data);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
		},
		p(ctx, dirty) {
			set_attributes(span, span_data = get_spread_update(span_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (109:1) {#if data.svg}
function create_if_block_1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$1(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] && create_if_block(ctx);

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
			if (/*data*/ ctx[0]) {
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

function instance$1($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		 {
			const iconData = checkIconState_1($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon_1(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
}

/* generated by Svelte v3.59.1 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[9] = list[i].link;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[9] = list[i].link;
	return child_ctx;
}

// (105:31) 
function create_if_block_4(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (103:6) {#if logo.title}
function create_if_block_3(ctx) {
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (110:6) {#each site_nav as { link }}
function create_each_block_1(ctx) {
	let a;
	let t_value = /*link*/ ctx[9].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "class", "link svelte-136lx2d");
			attr(a, "href", a_href_value = /*link*/ ctx[9].url);
			toggle_class(a, "active", /*link*/ ctx[9].url === window.location.pathname);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[9].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[9].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*site_nav, window*/ 2) {
				toggle_class(a, "active", /*link*/ ctx[9].url === window.location.pathname);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (122:31) 
function create_if_block_2(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, alt: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*logo*/ ctx[0].image.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && !src_url_equal(img.src, img_src_value = /*logo*/ ctx[0].image.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*logo*/ 1 && img_alt_value !== (img_alt_value = /*logo*/ ctx[0].image.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (120:6) {#if logo.title}
function create_if_block_1$1(ctx) {
	let t_value = /*logo*/ ctx[0].title + "";
	let t;

	return {
		c() {
			t = text(t_value);
		},
		l(nodes) {
			t = claim_text(nodes, t_value);
		},
		m(target, anchor) {
			insert_hydration(target, t, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*logo*/ 1 && t_value !== (t_value = /*logo*/ ctx[0].title + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(t);
		}
	};
}

// (132:4) {#if mobileNavOpen}
function create_if_block$1(ctx) {
	let nav;
	let t;
	let button;
	let icon;
	let nav_transition;
	let current;
	let mounted;
	let dispose;
	let each_value = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	icon = new Component$1({ props: { height: "25", icon: "bi:x-lg" } });

	return {
		c() {
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t = space();
			button = element("button");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			nav = claim_element(nodes, "NAV", { id: true, class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			t = claim_space(nav_nodes);

			button = claim_element(nav_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			nav_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(button, "id", "close");
			attr(button, "aria-label", "Close Navigation");
			attr(button, "class", "svelte-136lx2d");
			attr(nav, "id", "popup");
			attr(nav, "class", "svelte-136lx2d");
		},
		m(target, anchor) {
			insert_hydration(target, nav, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(nav, t);
			append_hydration(nav, button);
			mount_component(icon, button, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler_1*/ ctx[7]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2) {
				each_value = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, t);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			add_render_callback(() => {
				if (!current) return;
				if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, true);
				nav_transition.run(1);
			});

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			if (!nav_transition) nav_transition = create_bidirectional_transition(nav, fade, { duration: 200 }, false);
			nav_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(nav);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			if (detaching && nav_transition) nav_transition.end();
			mounted = false;
			dispose();
		}
	};
}

// (134:8) {#each site_nav as { link }}
function create_each_block(ctx) {
	let a;
	let t_value = /*link*/ ctx[9].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[9].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*site_nav*/ 2 && t_value !== (t_value = /*link*/ ctx[9].label + "")) set_data(t, t_value);

			if (dirty & /*site_nav*/ 2 && a_href_value !== (a_href_value = /*link*/ ctx[9].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$2(ctx) {
	let div2;
	let header;
	let div0;
	let a0;
	let t0;
	let nav;
	let t1;
	let div1;
	let a1;
	let t2;
	let button;
	let icon;
	let t3;
	let current;
	let mounted;
	let dispose;

	function select_block_type(ctx, dirty) {
		if (/*logo*/ ctx[0].title) return create_if_block_3;
		if (/*logo*/ ctx[0].image.url) return create_if_block_4;
	}

	let current_block_type = select_block_type(ctx);
	let if_block0 = current_block_type && current_block_type(ctx);
	let each_value_1 = /*site_nav*/ ctx[1];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	function select_block_type_1(ctx, dirty) {
		if (/*logo*/ ctx[0].title) return create_if_block_1$1;
		if (/*logo*/ ctx[0].image.url) return create_if_block_2;
	}

	let current_block_type_1 = select_block_type_1(ctx);
	let if_block1 = current_block_type_1 && current_block_type_1(ctx);

	icon = new Component$1({
			props: { height: "30", icon: "eva:menu-outline" }
		});

	let if_block2 = /*mobileNavOpen*/ ctx[2] && create_if_block$1(ctx);

	return {
		c() {
			div2 = element("div");
			header = element("header");
			div0 = element("div");
			a0 = element("a");
			if (if_block0) if_block0.c();
			t0 = space();
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t1 = space();
			div1 = element("div");
			a1 = element("a");
			if (if_block1) if_block1.c();
			t2 = space();
			button = element("button");
			create_component(icon.$$.fragment);
			t3 = space();
			if (if_block2) if_block2.c();
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			header = claim_element(div2_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div0 = claim_element(header_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			a0 = claim_element(div0_nodes, "A", { href: true, class: true });
			var a0_nodes = children(a0);
			if (if_block0) if_block0.l(a0_nodes);
			a0_nodes.forEach(detach);
			t0 = claim_space(div0_nodes);
			nav = claim_element(div0_nodes, "NAV", { class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			nav_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t1 = claim_space(header_nodes);
			div1 = claim_element(header_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a1 = claim_element(div1_nodes, "A", { href: true, class: true });
			var a1_nodes = children(a1);
			if (if_block1) if_block1.l(a1_nodes);
			a1_nodes.forEach(detach);
			t2 = claim_space(div1_nodes);
			button = claim_element(div1_nodes, "BUTTON", { id: true, "aria-label": true });
			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			if (if_block2) if_block2.l(div1_nodes);
			div1_nodes.forEach(detach);
			header_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a0, "href", "/");
			attr(a0, "class", "logo svelte-136lx2d");
			attr(nav, "class", "svelte-136lx2d");
			attr(div0, "class", "desktop-nav svelte-136lx2d");
			attr(a1, "href", "/");
			attr(a1, "class", "logo svelte-136lx2d");
			attr(button, "id", "open");
			attr(button, "aria-label", "Open mobile navigation");
			attr(div1, "class", "mobile-nav svelte-136lx2d");
			attr(header, "class", "section-container svelte-136lx2d");
			attr(div2, "class", "section");
			attr(div2, "id", "section-df1162be");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, header);
			append_hydration(header, div0);
			append_hydration(div0, a0);
			if (if_block0) if_block0.m(a0, null);
			append_hydration(div0, t0);
			append_hydration(div0, nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(header, t1);
			append_hydration(header, div1);
			append_hydration(div1, a1);
			if (if_block1) if_block1.m(a1, null);
			append_hydration(div1, t2);
			append_hydration(div1, button);
			mount_component(icon, button, null);
			append_hydration(div1, t3);
			if (if_block2) if_block2.m(div1, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*click_handler*/ ctx[6]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block0) {
				if_block0.p(ctx, dirty);
			} else {
				if (if_block0) if_block0.d(1);
				if_block0 = current_block_type && current_block_type(ctx);

				if (if_block0) {
					if_block0.c();
					if_block0.m(a0, null);
				}
			}

			if (dirty & /*site_nav, window*/ 2) {
				each_value_1 = /*site_nav*/ ctx[1];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}

			if (current_block_type_1 === (current_block_type_1 = select_block_type_1(ctx)) && if_block1) {
				if_block1.p(ctx, dirty);
			} else {
				if (if_block1) if_block1.d(1);
				if_block1 = current_block_type_1 && current_block_type_1(ctx);

				if (if_block1) {
					if_block1.c();
					if_block1.m(a1, null);
				}
			}

			if (/*mobileNavOpen*/ ctx[2]) {
				if (if_block2) {
					if_block2.p(ctx, dirty);

					if (dirty & /*mobileNavOpen*/ 4) {
						transition_in(if_block2, 1);
					}
				} else {
					if_block2 = create_if_block$1(ctx);
					if_block2.c();
					transition_in(if_block2, 1);
					if_block2.m(div1, null);
				}
			} else if (if_block2) {
				group_outros();

				transition_out(if_block2, 1, 1, () => {
					if_block2 = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			transition_in(if_block2);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			transition_out(if_block2);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div2);

			if (if_block0) {
				if_block0.d();
			}

			destroy_each(each_blocks, detaching);

			if (if_block1) {
				if_block1.d();
			}

			destroy_component(icon);
			if (if_block2) if_block2.d();
			mounted = false;
			dispose();
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { logo } = $$props;
	let { site_nav } = $$props;
	let mobileNavOpen = false;

	const click_handler = () => $$invalidate(2, mobileNavOpen = true);
	const click_handler_1 = () => $$invalidate(2, mobileNavOpen = false);

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(4, title = $$props.title);
		if ('description' in $$props) $$invalidate(5, description = $$props.description);
		if ('logo' in $$props) $$invalidate(0, logo = $$props.logo);
		if ('site_nav' in $$props) $$invalidate(1, site_nav = $$props.site_nav);
	};

	return [
		logo,
		site_nav,
		mobileNavOpen,
		favicon,
		title,
		description,
		click_handler,
		click_handler_1
	];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$2, safe_not_equal, {
			favicon: 3,
			title: 4,
			description: 5,
			logo: 0,
			site_nav: 1
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_if_block_1$2(ctx) {
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
			attr(span, "class", "svelte-owgiis");
			attr(a, "href", "#mainContent");
			attr(a, "class", "svelte-owgiis");
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

// (398:3) {#if slideno === 0}
function create_if_block$2(ctx) {
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

function create_fragment$3(ctx) {
	let div6;
	let section;
	let picture;
	let source0;
	let source0_srcset_value;
	let t0;
	let source1;
	let source1_srcset_value;
	let t1;
	let img;
	let img_src_value;
	let img_srcset_value;
	let picture_intro;
	let t2;
	let div5;
	let div0;
	let raw_value = /*texts*/ ctx[1][/*slideno*/ ctx[2]].first + "";
	let div0_intro;
	let t3;
	let div1;
	let t4_value = /*texts*/ ctx[1][/*slideno*/ ctx[2]].second + "";
	let t4;
	let div1_intro;
	let t5;
	let div2;
	let div2_intro;
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
	let if_block0 = /*texts*/ ctx[1][/*slideno*/ ctx[2]].button && create_if_block_1$2();
	let if_block1 = /*slideno*/ ctx[2] === 0 && create_if_block$2();

	return {
		c() {
			div6 = element("div");
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
			div6 = claim_element(nodes, "DIV", { class: true, id: true });
			var div6_nodes = children(div6);
			section = claim_element(div6_nodes, "SECTION", { class: true });
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
			div6_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(source0, "type", "image/avif");
			attr(source0, "sizes", "100vw");
			attr(source0, "srcset", source0_srcset_value = "\n\t\t\t  " + cdn + /*slides*/ ctx[0][/*slideno*/ ctx[2]].src + "-2x.avif 2128w, \n\t\t\t  " + cdn + /*slides*/ ctx[0][/*slideno*/ ctx[2]].src + "-1x.avif 1419w");
			attr(source1, "type", "image/webp");
			attr(source1, "sizes", "100vw");
			attr(source1, "srcset", source1_srcset_value = "\n\t\t\t  " + cdn + /*slides*/ ctx[0][/*slideno*/ ctx[2]].src + "-2x.webp 2128w, \n\t\t\t  " + cdn + /*slides*/ ctx[0][/*slideno*/ ctx[2]].src + "-1x.webp 1419w");
			attr(img, "alt", "hero");
			if (!src_url_equal(img.src, img_src_value = "" + (cdn + /*slides*/ ctx[0][/*slideno*/ ctx[2]].src + "-1x.jpg"))) attr(img, "src", img_src_value);
			attr(img, "srcset", img_srcset_value = "\n\t\t\t  " + cdn + /*slides*/ ctx[0][/*slideno*/ ctx[2]].src + "-2x.jpg 2128w, \n\t\t\t  " + cdn + /*slides*/ ctx[0][/*slideno*/ ctx[2]].src + "-1x.jpg 1419w");
			attr(img, "sizes", "100vw");
			attr(img, "height", "1061");
			attr(img, "width", "2126");
			set_style(img, "content-visibility", "auto");
			attr(img, "class", "svelte-owgiis");
			set_style(img, "--moveX", /*slides*/ ctx[0][/*slideno*/ ctx[2]].moveMobile.x);
			set_style(img, "--scale", /*slides*/ ctx[0][/*slideno*/ ctx[2]].moveMobile.scale);
			attr(picture, "class", "svelte-owgiis");
			set_style(picture, "--brightness", /*slides*/ ctx[0][/*slideno*/ ctx[2]].brightness || '');
			attr(div0, "class", "first svelte-owgiis");
			attr(div1, "class", "second svelte-owgiis");
			set_style(div1, "--length", /*texts*/ ctx[1][/*slideno*/ ctx[2]].second.length);
			attr(div2, "class", "buttonHero svelte-owgiis");
			attr(div3, "class", "premenu svelte-owgiis");
			attr(a0, "href", "/fotozony");
			attr(a0, "class", "svelte-owgiis");
			toggle_class(a0, "active", /*slideno*/ ctx[2] === 1);
			attr(a1, "href", "/tekhnika");
			attr(a1, "class", "svelte-owgiis");
			toggle_class(a1, "active", /*slideno*/ ctx[2] === 2);
			attr(a2, "href", "/kryla");
			attr(a2, "class", "svelte-owgiis");
			toggle_class(a2, "active", /*slideno*/ ctx[2] === 3);
			attr(a3, "href", "/sukni");
			attr(a3, "class", "svelte-owgiis");
			toggle_class(a3, "active", /*slideno*/ ctx[2] === 4);
			attr(a4, "href", "/pro");
			attr(a4, "class", "svelte-owgiis");
			toggle_class(a4, "active", /*slideno*/ ctx[2] === 5);
			attr(div4, "class", "menu svelte-owgiis");
			attr(div5, "class", "texts svelte-owgiis");
			attr(section, "class", "svelte-owgiis");
			attr(div6, "class", "section");
			attr(div6, "id", "section-a0a741e8");
		},
		m(target, anchor) {
			insert_hydration(target, div6, anchor);
			append_hydration(div6, section);
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
		p(new_ctx, [dirty]) {
			ctx = new_ctx;
		},
		i(local) {
			if (!picture_intro) {
				add_render_callback(() => {
					picture_intro = create_in_transition(picture, blur, { delay: 0, duration: 500 });
					picture_intro.start();
				});
			}

			if (!div0_intro) {
				add_render_callback(() => {
					div0_intro = create_in_transition(div0, fade$1, { delay: 250, duration: 1000 });
					div0_intro.start();
				});
			}

			if (!div1_intro) {
				add_render_callback(() => {
					div1_intro = create_in_transition(div1, fade$1, { delay: 500, duration: 1000 });
					div1_intro.start();
				});
			}

			if (!div2_intro) {
				add_render_callback(() => {
					div2_intro = create_in_transition(div2, scale, {
						start: 0.2,
						delay: 400,
						duration: 1000,
						easing: elasticInOut
					});

					div2_intro.start();
				});
			}
		},
		o: noop,
		d(detaching) {
			if (detaching) detach(div6);
			if (if_block0) if_block0.d();
			if (if_block1) if_block1.d();
		}
	};
}

const cdn = 'https://cdn.skystudio.uz.ua/old';

function elasticInOut(t) {
	return t < 0.5
	? 0.5 * Math.sin(+13.0 * Math.PI / 2 * 2.0 * t) * Math.pow(2.0, 10.0 * (2.0 * t - 1.0))
	: 0.5 * Math.sin(-13.0 * Math.PI / 2 * (2.0 * t - 1.0 + 1.0)) * Math.pow(2.0, -10.0 * (2.0 * t - 1.0)) + 1.0;
}

function blur(
	node,
{ delay = 0, duration = 400, easing = cubicInOut, amount = 5, opacity = 0 } = {}
) {
	const style = getComputedStyle(node);
	const target_opacity = +style.opacity;
	const f = style.filter === 'none' ? '' : style.filter;
	const od = target_opacity * (1 - opacity);
	const [value, unit] = split_css_unit(amount);

	return {
		delay,
		duration,
		easing,
		css: (_t, u) => `opacity: ${target_opacity - od * u}; filter: ${f} blur(${u * value}${unit});`
	};
}

function fade$1(node, { delay = 0, duration = 400, easing = linear } = {}) {
	const o = +getComputedStyle(node).opacity;

	return {
		delay,
		duration,
		easing,
		css: t => `opacity: ${t * o}`
	};
}

function scale(
	node,
{ delay = 0, duration = 400, easing = cubicOut, start = 0, opacity = 0 } = {}
) {
	const style = getComputedStyle(node);
	const target_opacity = +style.opacity;
	const transform = style.transform === 'none' ? '' : style.transform;
	const sd = 1 - start;
	const od = target_opacity * (1 - opacity);

	return {
		delay,
		duration,
		easing,
		css: (_t, u) => `
			transform: ${transform} scale(${1 - sd * u});
			opacity: ${target_opacity - od * u}
		`
	};
}

function instance$3($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { select_slide } = $$props;

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

	let slideno = select_slide ? parseInt(select_slide) : 0;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(4, title = $$props.title);
		if ('description' in $$props) $$invalidate(5, description = $$props.description);
		if ('select_slide' in $$props) $$invalidate(6, select_slide = $$props.select_slide);
	};

	return [slides, texts, slideno, favicon, title, description, select_slide];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			favicon: 3,
			title: 4,
			description: 5,
			select_slide: 6
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$4(ctx) {
	let div1;
	let div0;

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true, id: true });
			var div0_nodes = children(div0);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "section-container");
			attr(div0, "id", "mainContent");
			attr(div1, "class", "section");
			attr(div1, "id", "section-4cec6e6f");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
		},
		p: noop,
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
		}
	};
}

function instance$4($$self, $$props, $$invalidate) {
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

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$4, create_fragment$4, safe_not_equal, { favicon: 0, title: 1, description: 2 });
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$5(ctx) {
	let div4;
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
			div4 = element("div");
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
			div4 = claim_element(nodes, "DIV", { class: true, id: true });
			var div4_nodes = children(div4);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
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
			div4_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "text svelte-1p505uh");
			attr(span, "class", "svelte-1p505uh");
			attr(a, "href", a_href_value = /*button*/ ctx[1].url);
			attr(a, "class", "svelte-1p505uh");
			attr(div1, "class", "buttonWrapper svelte-1p505uh");
			attr(div2, "class", "infoLine toRight svelte-1p505uh");
			attr(div3, "class", "section-container");
			attr(div4, "class", "section");
			attr(div4, "id", "section-e63ef93d");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, div3);
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
			if (detaching) detach(div4);
		}
	};
}

function instance$5($$self, $$props, $$invalidate) {
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

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, create_fragment$5, safe_not_equal, {
			favicon: 2,
			title: 3,
			description: 4,
			heading: 0,
			button: 1
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_if_block$3(ctx) {
	let picture;

	function select_block_type(ctx, dirty) {
		if (/*x2*/ ctx[6]) return create_if_block_1$3;
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
function create_if_block_1$3(ctx) {
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

function create_fragment$6(ctx) {
	let if_block_anchor;
	let if_block = /*image*/ ctx[2] && create_if_block$3(ctx);

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
					if_block = create_if_block$3(ctx);
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

function instance$6($$self, $$props, $$invalidate) {
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

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$6, create_fragment$6, safe_not_equal, {
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

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[1] = list[i].title;
	child_ctx[2] = list[i].text;
	child_ctx[5] = list[i].picture;
	child_ctx[6] = list[i].date;
	return child_ctx;
}

// (260:2) {#each news as { title, text, picture, date }}
function create_each_block$1(ctx) {
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

	picture = new Component$6({
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

function create_fragment$7(ctx) {
	let div9;
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
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			div9 = element("div");
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
			div9 = claim_element(nodes, "DIV", { class: true, id: true });
			var div9_nodes = children(div9);
			div8 = claim_element(div9_nodes, "DIV", { class: true });
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
			div9_nodes.forEach(detach);
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
			attr(div9, "class", "section");
			attr(div9, "id", "section-d2e87603");
		},
		m(target, anchor) {
			insert_hydration(target, div9, anchor);
			append_hydration(div9, div8);
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
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
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
			if (detaching) detach(div9);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$7($$self, $$props, $$invalidate) {
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

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$7, create_fragment$7, safe_not_equal, {
			favicon: 3,
			title: 1,
			description: 4,
			news: 0,
			text: 2
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$8(ctx) {
	let div5;
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
			div5 = element("div");
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
			div5 = claim_element(nodes, "DIV", { class: true, id: true });
			var div5_nodes = children(div5);
			div4 = claim_element(div5_nodes, "DIV", { class: true });
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
			div5_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h3, "class", "svelte-wwjqoz");
			attr(div0, "class", "title svelte-wwjqoz");
			attr(div1, "class", "text svelte-wwjqoz");
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
			attr(img, "class", "svelte-wwjqoz");
			attr(picture, "class", "svelte-wwjqoz");
			attr(div2, "class", "image svelte-wwjqoz");
			attr(div3, "class", "blockWithImageAndButton svelte-wwjqoz");
			attr(div4, "class", "section-container");
			attr(div5, "class", "section");
			attr(div5, "id", "section-21e44ccf");
		},
		m(target, anchor) {
			insert_hydration(target, div5, anchor);
			append_hydration(div5, div4);
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
			if (detaching) detach(div5);
		}
	};
}

function instance$8($$self, $$props, $$invalidate) {
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

class Component$8 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$8, create_fragment$8, safe_not_equal, {
			favicon: 2,
			title: 3,
			description: 4,
			heading: 0,
			text: 1
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$9(ctx) {
	let div1;
	let div0;
	let iframe;
	let iframe_src_value;

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			iframe = element("iframe");
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			iframe = claim_element(div0_nodes, "IFRAME", {
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
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
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
			attr(iframe, "class", "svelte-fkbfxf");
			attr(div0, "class", "section-container");
			attr(div1, "class", "section");
			attr(div1, "id", "section-fe6920b8");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			append_hydration(div0, iframe);
		},
		p: noop,
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
		}
	};
}

function instance$9($$self, $$props, $$invalidate) {
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

class Component$9 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$9, create_fragment$9, safe_not_equal, { favicon: 0, title: 1, description: 2 });
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$a(ctx) {
	let div4;
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
			div4 = element("div");
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
			div4 = claim_element(nodes, "DIV", { class: true, id: true });
			var div4_nodes = children(div4);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
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
			div4_nodes.forEach(detach);
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
			attr(div3, "class", "section-container");
			attr(div4, "class", "section");
			attr(div4, "id", "section-8029bd1a");
		},
		m(target, anchor) {
			insert_hydration(target, div4, anchor);
			append_hydration(div4, div3);
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
			if (detaching) detach(div4);
		}
	};
}

function instance$a($$self, $$props, $$invalidate) {
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

class Component$a extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$a, create_fragment$a, safe_not_equal, { favicon: 0, title: 1, description: 2 });
	}
}

/* generated by Svelte v3.59.1 */

function get_each_context$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[5] = list[i].item;
	return child_ctx;
}

// (106:3) {#each links as {item}}
function create_each_block$2(ctx) {
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
			attr(a, "class", "footer svelte-b63oz0");
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

function create_fragment$b(ctx) {
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
		each_blocks[i] = create_each_block$2(get_each_context$2(ctx, each_value, i));
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
			attr(img, "class", "svelte-b63oz0");
			attr(a0, "href", "/");
			attr(a0, "class", "svelte-b63oz0");
			attr(div0, "class", "logo");
			attr(div1, "class", "nav svelte-b63oz0");
			attr(a1, "href", a1_href_value = "mailto:" + /*email*/ ctx[0]);
			attr(a1, "class", "svelte-b63oz0");
			attr(div2, "class", "info svelte-b63oz0");
			attr(div3, "class", "container svelte-b63oz0");
			attr(footer, "class", "svelte-b63oz0");
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
					const child_ctx = get_each_context$2(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$2(child_ctx);
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

function instance$b($$self, $$props, $$invalidate) {
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

class Component$b extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$b, create_fragment$b, safe_not_equal, {
			favicon: 2,
			title: 3,
			description: 4,
			email: 0,
			links: 1
		});
	}
}

/* generated by Svelte v3.59.1 */

function instance$c($$self, $$props, $$invalidate) {
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

class Component$c extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$c, null, safe_not_equal, { favicon: 0, title: 1, description: 2 });
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$c(ctx) {
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
	let t7;
	let component_8;
	let t8;
	let component_9;
	let t9;
	let component_10;
	let current;

	component_0 = new Component({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "Primo Skystudio",
				description: "Фотостудія в Ужгороді"
			}
		});

	component_1 = new Component$2({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "Primo Skystudio",
				description: "Фотостудія в Ужгороді",
				logo: {
					"image": {
						"alt": "",
						"src": "",
						"url": "",
						"size": null
					},
					"title": "BillionTrees"
				},
				site_nav: [
					{
						"link": {
							"url": "https://primosites.vercel.app/theme-nonprofit",
							"label": "Home"
						}
					},
					{
						"link": {
							"url": "https://primosites.vercel.app/about",
							"label": "About"
						}
					},
					{
						"link": {
							"url": "https://primosites.vercel.app/blog",
							"label": "Blog"
						}
					}
				]
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
				title: "Primo Skystudio",
				description: "Фотостудія в Ужгороді",
				select_slide: "0"
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
				title: "Primo Skystudio",
				description: "Фотостудія в Ужгороді"
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
				title: "Primo Skystudio",
				description: "Фотостудія в Ужгороді",
				heading: "Переглянути&nbsp;фотозони",
				button: {
					"url": "/fotozony#mainContent",
					"label": "Переглянути"
				}
			}
		});

	component_5 = new Component$7({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "Primo Skystudio",
				description: "Фотостудія в Ужгороді",
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

	component_6 = new Component$8({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "Primo Skystudio",
				description: "Фотостудія в Ужгороді",
				heading: "Правила оренди студії",
				text: {
					"html": "<ol>\n<li>Оренда студії відбувається без передоплати. Будь ласка, про зміни попереджуйте заздалегідь.</li>\n<li>У студії є змінне взуття на 6 людей. Якщо людей буде більше, вам треба подбати про своє змінне взуття. У нас на підлозі коврове покриття, тому спокійно можна бути в шкарпетках.</li>\n<li>Якщо ви будете фотографуватись у взутті, воно обовʼязково має бути чистим!</li>\n<li>Вся студія бронюється за вами лише за умови роботи одного фотографа. Якщо працює два фотографа паралельно на різних зонах, оплата подвоюється.</li>\n<li>Чай, кава - безкоштовні. Капучино - за наявності молока :)</li>\n<li>В разі пошкодження майна вам необхідно повністю компенсувати збитки. Витрати оплачуються вами відразу. Шукаємо ринкову ціну пошкодженої речі при вас.</li>\n<li>Якщо ви плануєте зйомку з тваринами чи просто приходите з ними, попереджуйте про їх наявність завчасно та узгоджуйте це питання з нами.</li>\n<li>Відверті зйомки — це добре, але категорично заборонені зйомки порнографічного характеру.</li>\n</ol>\n<h3 id=\"skystudio\">Дякуємо за розуміння! З радістю чекаємо вас в Sky Studio.</h3>",
					"markdown": "1. Оренда студії відбувається без передоплати. Будь ласка, про зміни попереджуйте заздалегідь.\n2. У студії є змінне взуття на 6 людей. Якщо людей буде більше, вам треба подбати про своє змінне взуття. У нас на підлозі коврове покриття, тому спокійно можна бути в шкарпетках.\n3. Якщо ви будете фотографуватись у взутті, воно обовʼязково має бути чистим!\n4. Вся студія бронюється за вами лише за умови роботи одного фотографа. Якщо працює два фотографа паралельно на різних зонах, оплата подвоюється.\n5. Чай, кава - безкоштовні. Капучино - за наявності молока :)\n6. В разі пошкодження майна вам необхідно повністю компенсувати збитки. Витрати оплачуються вами відразу. Шукаємо ринкову ціну пошкодженої речі при вас.\n7. Якщо ви плануєте зйомку з тваринами чи просто приходите з ними, попереджуйте про їх наявність завчасно та узгоджуйте це питання з нами.\n8. Відверті зйомки — це добре, але категорично заборонені зйомки порнографічного характеру.\n\n### Дякуємо за розуміння! З радістю чекаємо вас в Sky Studio."
				}
			}
		});

	component_7 = new Component$9({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "Primo Skystudio",
				description: "Фотостудія в Ужгороді"
			}
		});

	component_8 = new Component$a({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "Primo Skystudio",
				description: "Фотостудія в Ужгороді"
			}
		});

	component_9 = new Component$b({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "Sky Studio – Фотостудія з крилами в Ужгороді",
				description: "Фотостудія в Ужгороді",
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

	component_10 = new Component$c({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "Primo Skystudio",
				description: "Фотостудія в Ужгороді"
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
			t7 = space();
			create_component(component_8.$$.fragment);
			t8 = space();
			create_component(component_9.$$.fragment);
			t9 = space();
			create_component(component_10.$$.fragment);
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
			t7 = claim_space(nodes);
			claim_component(component_8.$$.fragment, nodes);
			t8 = claim_space(nodes);
			claim_component(component_9.$$.fragment, nodes);
			t9 = claim_space(nodes);
			claim_component(component_10.$$.fragment, nodes);
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
			insert_hydration(target, t7, anchor);
			mount_component(component_8, target, anchor);
			insert_hydration(target, t8, anchor);
			mount_component(component_9, target, anchor);
			insert_hydration(target, t9, anchor);
			mount_component(component_10, target, anchor);
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
			transition_in(component_8.$$.fragment, local);
			transition_in(component_9.$$.fragment, local);
			transition_in(component_10.$$.fragment, local);
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
			transition_out(component_8.$$.fragment, local);
			transition_out(component_9.$$.fragment, local);
			transition_out(component_10.$$.fragment, local);
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
			if (detaching) detach(t7);
			destroy_component(component_8, detaching);
			if (detaching) detach(t8);
			destroy_component(component_9, detaching);
			if (detaching) detach(t9);
			destroy_component(component_10, detaching);
		}
	};
}

class Component$d extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$c, safe_not_equal, {});
	}
}

export default Component$d;
