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
function split_css_unit$1(value) {
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
			t = text("@font-face {\n  font-family: 'ProximaNova';\n  font-style: normal;\n  font-weight: 300;\n  font-stretch: 100%;\n  font-display: swap;\n  src: url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Regular.woff2) format('woff2'),\n    url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Regular.ttf);\n}\n\n@font-face {\n  font-family: 'ProximaNova';\n  font-style: normal;\n  font-weight: 600;\n  font-stretch: 100%;\n  font-display: swap;\n  src: url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Bold.woff2) format('woff2'),\n    url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Bold.ttf);\n}\n\n@font-face {\n  font-family: 'ProximaNova';\n  font-style: normal;\n  font-weight: 900;\n  font-stretch: 100%;\n  font-display: swap;\n  src: url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Black.woff2) format('woff2'),\n    url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Black.ttf);\n}\n\n@font-face {\n  font-family: 'NotoSerif';\n  font-style: normal;\n  font-weight: 700;\n  font-stretch: 100%;\n  font-display: swap;\n  src: url(https://cdn.skystudio.uz.ua/old/fonts/Noto_Serif/NotoSerif-Regular.ttf);\n}\n\n/* Reset & standardize default styles */\n/*@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;*/\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options\n  --color-accent: #004700;\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 0;\n  --border-color: #e0e1e1;\n  */\n  --color-accent: #FEC93C;\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 0;\n  --border-color: #294c80;\n\n  --darkColor: #294c80;\n  --lightColor: #2d8fc5;\n  --accentColor: #FEC93C;\n  --accentDarkerColor: #FEC93C;\n  --font1: \"ProximaNova\", sans-serif;\n  --font2: \"NotoSerif\", serif;\n\n  --color: #0f0f16;\n  --colorGray: #b6b6d2;\n  --zoom: 0.9;\n}\n\nhtml {\n  /* zoom: var(--zoom); */\n}\n\nhtml,\nbody {\n  background-color: var(--darkColor);\n}\n\n\n.noscroll {\n  overflow: hidden;\n}\n\n\n\n/* Root element (use instead of `body`) */\n#page {\n  zoom: var(--zoom);\n  scroll-behavior: smooth;\n  scroll-padding: 6em;\n  padding: 0;\n  margin: 0;\n  background-color: white;\n  font-size: 16px;\n\n\n  color: var(--color);\n\n\n  font-size: 16px;\n  font-family: var(--font1);\n  font-weight: 300;\n}\n#page a {\n    text-decoration: none;\n  }\n@media (hover: hover) and (pointer: fine) {\n    #page a:hover {\n      text-decoration: none;\n    }\n  }\n\n/* Elements */\n.section {\n  background-color: white;\n}\n\n.section-container {\n  max-width: 1200px;\n  margin: 0 auto;\n  width: auto;\n  padding-bottom: 3rem;\n}\n\n@media screen and (min-width: 768px) {\n\n.section-container {\n    width: calc(100% - 2rem)\n}\n  }\n\n.section-container.no-bottom-padding {\n    padding-bottom: 0;\n  }\n\na.link {\n  line-height: 1.3;\n\n  border-bottom: 2px solid var(--color-accent);\n  transform: translateY(-2px);\n  /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: 2.5rem;\n  line-height: 1.15;\n\n}\n\n.button {\n  color: white;\n  background: var(--color-accent, rebeccapurple);\n  border-radius: 0;\n  padding: 18px 24px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0;\n}\n\n/* reset */\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent, rebeccapurple);\n  }\n\n/* Content Section */\n.content {\n  max-width: 900px;\n  margin: 0 auto;\n  padding: 3rem 2rem;\n}\n.content p {\n    margin-bottom: 1rem;\n    line-height: 1.5;\n  }\n.content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n.content a.link {\n    line-height: 1.3;\n    font-weight: 500;\n    border-bottom: 2px solid var(--color-accent);\n    transform: translateY(-2px);\n    /* move link back into place */\n    transition: var(--transition, 0.1s border);\n  }\n.content a.link:hover {\n      border-color: transparent;\n    }\n.content h1 {\n    font-size: 3rem;\n    font-weight: 500;\n    line-height: 1.1;\n    margin-bottom: 1.5rem;\n  }\n.content h2 {\n    font-size: 2.5rem;\n    font-weight: 500;\n    margin-bottom: 1rem;\n  }\n.content h3 {\n    font-size: 2rem;\n    font-weight: 500;\n    margin-bottom: 1rem;\n  }\n.content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.content blockquote {\n    padding: 2rem;\n    margin-top: 1.5rem;\n    margin-bottom: 1.5rem;\n    border-left: 5px solid var(--color-accent);\n  }");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-1g4smfr', document.head);

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
			t = claim_text(style_nodes, "@font-face {\n  font-family: 'ProximaNova';\n  font-style: normal;\n  font-weight: 300;\n  font-stretch: 100%;\n  font-display: swap;\n  src: url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Regular.woff2) format('woff2'),\n    url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Regular.ttf);\n}\n\n@font-face {\n  font-family: 'ProximaNova';\n  font-style: normal;\n  font-weight: 600;\n  font-stretch: 100%;\n  font-display: swap;\n  src: url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Bold.woff2) format('woff2'),\n    url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Bold.ttf);\n}\n\n@font-face {\n  font-family: 'ProximaNova';\n  font-style: normal;\n  font-weight: 900;\n  font-stretch: 100%;\n  font-display: swap;\n  src: url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Black.woff2) format('woff2'),\n    url(https://cdn.skystudio.uz.ua/old/fonts/used/ProximaNova-Black.ttf);\n}\n\n@font-face {\n  font-family: 'NotoSerif';\n  font-style: normal;\n  font-weight: 700;\n  font-stretch: 100%;\n  font-display: swap;\n  src: url(https://cdn.skystudio.uz.ua/old/fonts/Noto_Serif/NotoSerif-Regular.ttf);\n}\n\n/* Reset & standardize default styles */\n/*@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\") layer;*/\n\n/* Design tokens (apply to components) */\n:root {\n  /* Custom theme options\n  --color-accent: #004700;\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 0;\n  --border-color: #e0e1e1;\n  */\n  --color-accent: #FEC93C;\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 0;\n  --border-color: #294c80;\n\n  --darkColor: #294c80;\n  --lightColor: #2d8fc5;\n  --accentColor: #FEC93C;\n  --accentDarkerColor: #FEC93C;\n  --font1: \"ProximaNova\", sans-serif;\n  --font2: \"NotoSerif\", serif;\n\n  --color: #0f0f16;\n  --colorGray: #b6b6d2;\n  --zoom: 0.9;\n}\n\nhtml {\n  /* zoom: var(--zoom); */\n}\n\nhtml,\nbody {\n  background-color: var(--darkColor);\n}\n\n\n.noscroll {\n  overflow: hidden;\n}\n\n\n\n/* Root element (use instead of `body`) */\n#page {\n  zoom: var(--zoom);\n  scroll-behavior: smooth;\n  scroll-padding: 6em;\n  padding: 0;\n  margin: 0;\n  background-color: white;\n  font-size: 16px;\n\n\n  color: var(--color);\n\n\n  font-size: 16px;\n  font-family: var(--font1);\n  font-weight: 300;\n}\n#page a {\n    text-decoration: none;\n  }\n@media (hover: hover) and (pointer: fine) {\n    #page a:hover {\n      text-decoration: none;\n    }\n  }\n\n/* Elements */\n.section {\n  background-color: white;\n}\n\n.section-container {\n  max-width: 1200px;\n  margin: 0 auto;\n  width: auto;\n  padding-bottom: 3rem;\n}\n\n@media screen and (min-width: 768px) {\n\n.section-container {\n    width: calc(100% - 2rem)\n}\n  }\n\n.section-container.no-bottom-padding {\n    padding-bottom: 0;\n  }\n\na.link {\n  line-height: 1.3;\n\n  border-bottom: 2px solid var(--color-accent);\n  transform: translateY(-2px);\n  /* move link back into place */\n  transition: var(--transition, 0.1s border);\n}\n\na.link:hover {\n    border-color: transparent;\n  }\n\n.heading {\n  font-size: 2.5rem;\n  line-height: 1.15;\n\n}\n\n.button {\n  color: white;\n  background: var(--color-accent, rebeccapurple);\n  border-radius: 0;\n  padding: 18px 24px;\n  transition: var(--transition, 0.1s box-shadow);\n  border: 0;\n}\n\n/* reset */\n\n.button:hover {\n    box-shadow: 0 0 0 2px var(--color-accent, rebeccapurple);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent, rebeccapurple);\n  }\n\n/* Content Section */\n.content {\n  max-width: 900px;\n  margin: 0 auto;\n  padding: 3rem 2rem;\n}\n.content p {\n    margin-bottom: 1rem;\n    line-height: 1.5;\n  }\n.content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n.content a.link {\n    line-height: 1.3;\n    font-weight: 500;\n    border-bottom: 2px solid var(--color-accent);\n    transform: translateY(-2px);\n    /* move link back into place */\n    transition: var(--transition, 0.1s border);\n  }\n.content a.link:hover {\n      border-color: transparent;\n    }\n.content h1 {\n    font-size: 3rem;\n    font-weight: 500;\n    line-height: 1.1;\n    margin-bottom: 1.5rem;\n  }\n.content h2 {\n    font-size: 2.5rem;\n    font-weight: 500;\n    margin-bottom: 1rem;\n  }\n.content h3 {\n    font-size: 2rem;\n    font-weight: 500;\n    margin-bottom: 1rem;\n  }\n.content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n.content blockquote {\n    padding: 2rem;\n    margin-top: 1.5rem;\n    margin-bottom: 1.5rem;\n    border-left: 5px solid var(--color-accent);\n  }");
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
	let { slide_number } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(1, title = $$props.title);
		if ('description' in $$props) $$invalidate(2, description = $$props.description);
		if ('slide_number' in $$props) $$invalidate(3, slide_number = $$props.slide_number);
	};

	return [favicon, title, description, slide_number];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance, create_fragment, safe_not_equal, {
			favicon: 0,
			title: 1,
			description: 2,
			slide_number: 3
		});
	}
}

function circIn(t) {
    return 1.0 - Math.sqrt(1.0 - t * t);
}
function circOut(t) {
    return Math.sqrt(1 - --t * t);
}
function cubicOut$1(t) {
    const f = t - 1.0;
    return f * f * f + 1.0;
}

function fly(node, { delay = 0, duration = 400, easing = cubicOut$1, x = 0, y = 0, opacity = 0 } = {}) {
    const style = getComputedStyle(node);
    const target_opacity = +style.opacity;
    const transform = style.transform === 'none' ? '' : style.transform;
    const od = target_opacity * (1 - opacity);
    const [xValue, xUnit] = split_css_unit$1(x);
    const [yValue, yUnit] = split_css_unit$1(y);
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

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[14] = list[i].item;
	child_ctx[16] = i;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[14] = list[i].item;
	child_ctx[16] = i;
	return child_ctx;
}

// (354:0) {#if openMenu}
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
	let swipeToClose_action;
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
			attr(img0, "class", "svelte-5fxekz");
			attr(button, "class", "svelte-5fxekz");
			attr(div0, "class", "cross svelte-5fxekz");
			if (!src_url_equal(img1.src, img1_src_value = "https://cdn.skystudio.uz.ua/old/skystudio_logo.svg")) attr(img1, "src", img1_src_value);
			attr(img1, "alt", "Logo SkyStudio");
			attr(img1, "class", "svelte-5fxekz");
			attr(a0, "href", "/");
			attr(a0, "class", "svelte-5fxekz");
			attr(div1, "class", "logo svelte-5fxekz");
			attr(ul, "class", "svelte-5fxekz");
			attr(img2, "alt", "fb icon");
			if (!src_url_equal(img2.src, img2_src_value = "https://cdn.skystudio.uz.ua/old/icons/phone.svg")) attr(img2, "src", img2_src_value);
			attr(img2, "class", "svelte-5fxekz");
			attr(a1, "rel", "noreferrer");
			attr(a1, "href", "tel:+380950889787");
			attr(a1, "class", "svelte-5fxekz");
			attr(img3, "alt", "instagram icon");
			if (!src_url_equal(img3.src, img3_src_value = "https://cdn.skystudio.uz.ua/old/icons/insta.svg")) attr(img3, "src", img3_src_value);
			attr(img3, "class", "svelte-5fxekz");
			set_style(img3, "--size", `1.7rem`);
			attr(a2, "target", "_blank");
			attr(a2, "rel", "noreferrer");
			attr(a2, "href", "https://www.instagram.com/sky_studio_uzh/");
			attr(a2, "class", "svelte-5fxekz");
			attr(img4, "alt", "fb icon");
			if (!src_url_equal(img4.src, img4_src_value = "https://cdn.skystudio.uz.ua/old/icons/fb.svg")) attr(img4, "src", img4_src_value);
			attr(img4, "class", "svelte-5fxekz");
			attr(a3, "target", "_blank");
			attr(a3, "rel", "noreferrer");
			attr(a3, "href", "https://www.facebook.com/skystudio.uz");
			attr(a3, "class", "svelte-5fxekz");
			attr(img5, "alt", "telegram icon");
			if (!src_url_equal(img5.src, img5_src_value = "https://cdn.skystudio.uz.ua/old/icons/telegram.svg")) attr(img5, "src", img5_src_value);
			attr(img5, "class", "svelte-5fxekz");
			set_style(img5, "--size", `1.4rem`);
			attr(a4, "target", "_blank");
			attr(a4, "rel", "noreferrer");
			attr(a4, "href", "https://t.me/macwings");
			attr(a4, "class", "svelte-5fxekz");
			attr(img6, "alt", "youtube icon");
			if (!src_url_equal(img6.src, img6_src_value = "https://cdn.skystudio.uz.ua/old/icons/youtube.svg")) attr(img6, "src", img6_src_value);
			attr(img6, "class", "svelte-5fxekz");
			set_style(img6, "--size", `1.4rem`);
			attr(a5, "target", "_blank");
			attr(a5, "rel", "noreferrer");
			attr(a5, "href", "https://youtube.com/@sky_studio_uzh");
			attr(a5, "class", "svelte-5fxekz");
			attr(div2, "class", "social svelte-5fxekz");
			attr(div3, "class", "phone svelte-5fxekz");
			attr(div4, "class", "main svelte-5fxekz");
			attr(div5, "class", "footer svelte-5fxekz");
			attr(div6, "class", "mobileMenu svelte-5fxekz");
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
					listen(button, "click", /*click_handler*/ ctx[11]),
					action_destroyer(swipeToClose_action = /*swipeToClose*/ ctx[4].call(null, div6)),
					listen(div6, "swiperight", /*swiperight_handler*/ ctx[12])
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

// (370:7) {#each links as {item}
function create_each_block_1(ctx) {
	let li;
	let a;
	let t_value = /*item*/ ctx[14].label + "";
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
			attr(a, "aria-current", a_aria_current_value = /*checkCurrent*/ ctx[3](/*index*/ ctx[16]));
			attr(a, "href", a_href_value = /*item*/ ctx[14].url);
			attr(a, "title", a_title_value = /*item*/ ctx[14].label);
			attr(a, "class", "svelte-5fxekz");
			toggle_class(a, "current", /*checkCurrent*/ ctx[3](/*index*/ ctx[16]));
			attr(li, "class", "svelte-5fxekz");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, a);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*links*/ 1 && t_value !== (t_value = /*item*/ ctx[14].label + "")) set_data(t, t_value);

			if (dirty & /*links*/ 1 && a_href_value !== (a_href_value = /*item*/ ctx[14].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*links*/ 1 && a_title_value !== (a_title_value = /*item*/ ctx[14].label)) {
				attr(a, "title", a_title_value);
			}
		},
		d(detaching) {
			if (detaching) detach(li);
		}
	};
}

// (413:4) {:else}
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
			attr(img, "class", "svelte-5fxekz");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (407:4) {#if scrollY > scrollTrigger}
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
			attr(img, "class", "svelte-5fxekz");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (419:13) {#each links as {item}
function create_each_block(ctx) {
	let a;
	let t_value = /*item*/ ctx[14].label + "";
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
			attr(a, "href", a_href_value = /*item*/ ctx[14].url);
			attr(a, "title", a_title_value = /*item*/ ctx[14].label);
			attr(a, "class", "svelte-5fxekz");
			toggle_class(a, "current", /*checkCurrent*/ ctx[3](/*index*/ ctx[16]));
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*links*/ 1 && t_value !== (t_value = /*item*/ ctx[14].label + "")) set_data(t, t_value);

			if (dirty & /*links*/ 1 && a_href_value !== (a_href_value = /*item*/ ctx[14].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*links*/ 1 && a_title_value !== (a_title_value = /*item*/ ctx[14].label)) {
				attr(a, "title", a_title_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$1(ctx) {
	let scrolling = false;

	let clear_scrolling = () => {
		scrolling = false;
	};

	let scrolling_timeout;
	let div6;
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
	add_render_callback(/*onwindowscroll*/ ctx[10]);
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
			div6 = element("div");
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
			div6 = claim_element(nodes, "DIV", { class: true, id: true });
			var div6_nodes = children(div6);
			if (if_block0) if_block0.l(div6_nodes);
			t0 = claim_space(div6_nodes);
			header = claim_element(div6_nodes, "HEADER", { class: true });
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
			div6_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a0, "href", "/");
			attr(a0, "class", "svelte-5fxekz");
			attr(div0, "class", "logo svelte-5fxekz");
			attr(div1, "class", "nav svelte-5fxekz");
			attr(img0, "alt", "fb icon");
			if (!src_url_equal(img0.src, img0_src_value = "https://cdn.skystudio.uz.ua/old/icons/phone.svg")) attr(img0, "src", img0_src_value);
			attr(img0, "class", "svelte-5fxekz");
			attr(a1, "rel", "noreferrer");
			attr(a1, "href", "tel:+380950889787");
			attr(a1, "class", "svelte-5fxekz");
			attr(img1, "alt", "instagram icon");
			if (!src_url_equal(img1.src, img1_src_value = "https://cdn.skystudio.uz.ua/old/icons/insta.svg")) attr(img1, "src", img1_src_value);
			attr(img1, "class", "svelte-5fxekz");
			set_style(img1, "--size", `1.5rem`);
			attr(a2, "target", "_blank");
			attr(a2, "rel", "noreferrer");
			attr(a2, "href", "https://www.instagram.com/sky_studio_uzh/");
			attr(a2, "class", "svelte-5fxekz");
			attr(img2, "alt", "fb icon");
			if (!src_url_equal(img2.src, img2_src_value = "https://cdn.skystudio.uz.ua/old/icons/fb.svg")) attr(img2, "src", img2_src_value);
			attr(img2, "class", "svelte-5fxekz");
			attr(a3, "target", "_blank");
			attr(a3, "rel", "noreferrer");
			attr(a3, "href", "https://www.facebook.com/skystudio.uz");
			attr(a3, "class", "svelte-5fxekz");
			attr(img3, "alt", "youtube icon");
			if (!src_url_equal(img3.src, img3_src_value = "https://cdn.skystudio.uz.ua/old/icons/youtube.svg")) attr(img3, "src", img3_src_value);
			attr(img3, "class", "svelte-5fxekz");
			attr(a4, "target", "_blank");
			attr(a4, "rel", "noreferrer");
			attr(a4, "href", "https://youtube.com/@sky_studio_uzh");
			attr(a4, "class", "svelte-5fxekz");
			attr(div2, "class", "social svelte-5fxekz");
			attr(div3, "class", "langs");
			attr(img4, "alt", "burger icon");
			if (!src_url_equal(img4.src, img4_src_value = "https://cdn.skystudio.uz.ua/old/icons/hamburger.svg")) attr(img4, "src", img4_src_value);
			attr(img4, "class", "svelte-5fxekz");
			attr(button, "class", "svelte-5fxekz");
			attr(div4, "class", "burger svelte-5fxekz");
			attr(div5, "class", "container svelte-5fxekz");
			attr(header, "class", "svelte-5fxekz");
			toggle_class(header, "scrolled", /*scrollY*/ ctx[1] > scrollTrigger);
			attr(div6, "class", "section");
			attr(div6, "id", "section-d2e0b991");
		},
		m(target, anchor) {
			insert_hydration(target, div6, anchor);
			if (if_block0) if_block0.m(div6, null);
			append_hydration(div6, t0);
			append_hydration(div6, header);
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
					listen(window, "scroll", () => {
						scrolling = true;
						clearTimeout(scrolling_timeout);
						scrolling_timeout = setTimeout(clear_scrolling, 100);
						/*onwindowscroll*/ ctx[10]();
					}),
					listen(button, "click", /*click_handler_1*/ ctx[13])
				];

				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*scrollY*/ 2 && !scrolling) {
				scrolling = true;
				clearTimeout(scrolling_timeout);
				scrollTo(window.pageXOffset, /*scrollY*/ ctx[1]);
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
					if_block0.m(div6, t0);
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
			if (detaching) detach(div6);
			if (if_block0) if_block0.d();
			if_block1.d();
			destroy_each(each_blocks, detaching);
			mounted = false;
			run_all(dispose);
		}
	};
}

const scrollTrigger = 200;

function instance$1($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { slide_number } = $$props;
	let { links } = $$props;
	let scrollY = 0;
	let openMenu = false;

	function checkCurrent(index) {
		if (typeof slide_number !== 'undefined' && parseInt(slide_number) === index) return true;
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
		$$invalidate(1, scrollY = window.pageYOffset);
	}

	const click_handler = () => $$invalidate(2, openMenu = false);
	const swiperight_handler = () => $$invalidate(2, openMenu = false);
	const click_handler_1 = () => $$invalidate(2, openMenu = true);

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(5, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(6, title = $$props.title);
		if ('description' in $$props) $$invalidate(7, description = $$props.description);
		if ('slide_number' in $$props) $$invalidate(8, slide_number = $$props.slide_number);
		if ('links' in $$props) $$invalidate(0, links = $$props.links);
	};

	return [
		links,
		scrollY,
		openMenu,
		checkCurrent,
		swipeToClose,
		favicon,
		title,
		description,
		slide_number,
		swipable,
		onwindowscroll,
		click_handler,
		swiperight_handler,
		click_handler_1
	];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$1, create_fragment$1, safe_not_equal, {
			favicon: 5,
			title: 6,
			description: 7,
			slide_number: 8,
			links: 0,
			swipable: 9
		});
	}

	get swipable() {
		return this.$$.ctx[9];
	}
}

/* generated by Svelte v3.59.1 */

function create_if_block_1$1(ctx) {
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

// (399:3) {#if slideno === 0}
function create_if_block$1(ctx) {
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

function create_fragment$2(ctx) {
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
	let if_block0 = /*texts*/ ctx[1][/*slideno*/ ctx[2]].button && create_if_block_1$1();
	let if_block1 = /*slideno*/ ctx[2] === 0 && create_if_block$1();

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
			attr(div6, "class", "section");
			attr(div6, "id", "section-80316739");
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
					div0_intro = create_in_transition(div0, fade, { delay: 250, duration: 1000 });
					div0_intro.start();
				});
			}

			if (!div1_intro) {
				add_render_callback(() => {
					div1_intro = create_in_transition(div1, fade, { delay: 500, duration: 1000 });
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

function fade(node, { delay = 0, duration = 400, easing = linear } = {}) {
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

function instance$2($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { slide_number } = $$props;

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
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(4, title = $$props.title);
		if ('description' in $$props) $$invalidate(5, description = $$props.description);
		if ('slide_number' in $$props) $$invalidate(6, slide_number = $$props.slide_number);
	};

	return [slides, texts, slideno, favicon, title, description, slide_number];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$2, safe_not_equal, {
			favicon: 3,
			title: 4,
			description: 5,
			slide_number: 6
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$3(ctx) {
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
			attr(div1, "id", "section-f93d8656");
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

function instance$3($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { slide_number } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(1, title = $$props.title);
		if ('description' in $$props) $$invalidate(2, description = $$props.description);
		if ('slide_number' in $$props) $$invalidate(3, slide_number = $$props.slide_number);
	};

	return [favicon, title, description, slide_number];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			favicon: 0,
			title: 1,
			description: 2,
			slide_number: 3
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$4(ctx) {
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
			attr(div4, "id", "section-6ac3a884");
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

function instance$4($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { slide_number } = $$props;
	let { heading } = $$props;
	let { button } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(2, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(3, title = $$props.title);
		if ('description' in $$props) $$invalidate(4, description = $$props.description);
		if ('slide_number' in $$props) $$invalidate(5, slide_number = $$props.slide_number);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('button' in $$props) $$invalidate(1, button = $$props.button);
	};

	return [heading, button, favicon, title, description, slide_number];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$4, create_fragment$4, safe_not_equal, {
			favicon: 2,
			title: 3,
			description: 4,
			slide_number: 5,
			heading: 0,
			button: 1
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_if_block$2(ctx) {
	let picture;

	function select_block_type(ctx, dirty) {
		if (/*x2*/ ctx[6]) return create_if_block_1$2;
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
function create_if_block_1$2(ctx) {
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

function create_fragment$5(ctx) {
	let if_block_anchor;
	let if_block = /*image*/ ctx[2] && create_if_block$2(ctx);

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
					if_block = create_if_block$2(ctx);
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

function instance$5($$self, $$props, $$invalidate) {
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

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, create_fragment$5, safe_not_equal, {
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
	child_ctx[6] = list[i].picture;
	child_ctx[7] = list[i].date;
	return child_ctx;
}

// (261:2) {#each news as { title, text, picture, date }}
function create_each_block$1(ctx) {
	let div4;
	let div0;
	let t0_value = /*title*/ ctx[1] + "";
	let t0;
	let t1;
	let div1;
	let t2_value = /*date*/ ctx[7] + "";
	let t2;
	let t3;
	let div2;
	let raw_value = /*text*/ ctx[2] + "";
	let t4;
	let div3;
	let picture;
	let current;

	picture = new Component$5({
			props: {
				cdn: "https://cdn.skystudio.uz.ua/old",
				x2: false,
				width: 960,
				heigh: 1280,
				loading: "eager",
				path: "/i/news/" + /*date*/ ctx[7],
				image: /*picture*/ ctx[6]
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
			if ((!current || dirty & /*news*/ 1) && t2_value !== (t2_value = /*date*/ ctx[7] + "")) set_data(t2, t2_value);
			if ((!current || dirty & /*news*/ 1) && raw_value !== (raw_value = /*text*/ ctx[2] + "")) div2.innerHTML = raw_value;			const picture_changes = {};
			if (dirty & /*news*/ 1) picture_changes.path = "/i/news/" + /*date*/ ctx[7];
			if (dirty & /*news*/ 1) picture_changes.image = /*picture*/ ctx[6];
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

function create_fragment$6(ctx) {
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
			attr(div9, "id", "section-432b303e");
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

function instance$6($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { slide_number } = $$props;
	let { news } = $$props;
	let { text } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(1, title = $$props.title);
		if ('description' in $$props) $$invalidate(4, description = $$props.description);
		if ('slide_number' in $$props) $$invalidate(5, slide_number = $$props.slide_number);
		if ('news' in $$props) $$invalidate(0, news = $$props.news);
		if ('text' in $$props) $$invalidate(2, text = $$props.text);
	};

	return [news, title, text, favicon, description, slide_number];
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$6, create_fragment$6, safe_not_equal, {
			favicon: 3,
			title: 1,
			description: 4,
			slide_number: 5,
			news: 0,
			text: 2
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$7(ctx) {
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
			attr(div5, "id", "section-05292821");
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

function instance$7($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { slide_number } = $$props;
	let { heading } = $$props;
	let { text } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(2, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(3, title = $$props.title);
		if ('description' in $$props) $$invalidate(4, description = $$props.description);
		if ('slide_number' in $$props) $$invalidate(5, slide_number = $$props.slide_number);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('text' in $$props) $$invalidate(1, text = $$props.text);
	};

	return [heading, text, favicon, title, description, slide_number];
}

class Component$7 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$7, create_fragment$7, safe_not_equal, {
			favicon: 2,
			title: 3,
			description: 4,
			slide_number: 5,
			heading: 0,
			text: 1
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$8(ctx) {
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
			attr(div1, "id", "section-f61b7893");
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

function instance$8($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { slide_number } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(1, title = $$props.title);
		if ('description' in $$props) $$invalidate(2, description = $$props.description);
		if ('slide_number' in $$props) $$invalidate(3, slide_number = $$props.slide_number);
	};

	return [favicon, title, description, slide_number];
}

class Component$8 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$8, create_fragment$8, safe_not_equal, {
			favicon: 0,
			title: 1,
			description: 2,
			slide_number: 3
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$9(ctx) {
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
			attr(div4, "id", "section-647dd1a5");
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

function instance$9($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { slide_number } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(1, title = $$props.title);
		if ('description' in $$props) $$invalidate(2, description = $$props.description);
		if ('slide_number' in $$props) $$invalidate(3, slide_number = $$props.slide_number);
	};

	return [favicon, title, description, slide_number];
}

class Component$9 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$9, create_fragment$9, safe_not_equal, {
			favicon: 0,
			title: 1,
			description: 2,
			slide_number: 3
		});
	}
}

/* generated by Svelte v3.59.1 */

function get_each_context$2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[7] = list[i].item;
	child_ctx[9] = i;
	return child_ctx;
}

// (111:3) {#each links as {item}
function create_each_block$2(ctx) {
	let a;
	let t_value = /*item*/ ctx[7].label + "";
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
			attr(a, "class", "lighter svelte-b63oz0");
			attr(a, "href", a_href_value = /*item*/ ctx[7].url);
			attr(a, "title", a_title_value = /*item*/ ctx[7].label);
			toggle_class(a, "current", /*checkCurrent*/ ctx[2](/*index*/ ctx[9]));
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*links*/ 2 && t_value !== (t_value = /*item*/ ctx[7].label + "")) set_data(t, t_value);

			if (dirty & /*links*/ 2 && a_href_value !== (a_href_value = /*item*/ ctx[7].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*links*/ 2 && a_title_value !== (a_title_value = /*item*/ ctx[7].label)) {
				attr(a, "title", a_title_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$a(ctx) {
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
			attr(div4, "id", "section-051b42c3");
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
			if (dirty & /*links, checkCurrent*/ 6) {
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

function instance$a($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { slide_number } = $$props;
	let { email } = $$props;
	let { links } = $$props;

	function checkCurrent(index) {
		if (typeof slide_number !== 'undefined' && parseInt(slide_number) === index) return true;
		return false;
	}

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(3, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(4, title = $$props.title);
		if ('description' in $$props) $$invalidate(5, description = $$props.description);
		if ('slide_number' in $$props) $$invalidate(6, slide_number = $$props.slide_number);
		if ('email' in $$props) $$invalidate(0, email = $$props.email);
		if ('links' in $$props) $$invalidate(1, links = $$props.links);
	};

	return [email, links, checkCurrent, favicon, title, description, slide_number];
}

class Component$a extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$a, create_fragment$a, safe_not_equal, {
			favicon: 3,
			title: 4,
			description: 5,
			slide_number: 6,
			email: 0,
			links: 1
		});
	}
}

/* generated by Svelte v3.59.1 */

function instance$b($$self, $$props, $$invalidate) {
	let { favicon } = $$props;
	let { title } = $$props;
	let { description } = $$props;
	let { slide_number } = $$props;

	$$self.$$set = $$props => {
		if ('favicon' in $$props) $$invalidate(0, favicon = $$props.favicon);
		if ('title' in $$props) $$invalidate(1, title = $$props.title);
		if ('description' in $$props) $$invalidate(2, description = $$props.description);
		if ('slide_number' in $$props) $$invalidate(3, slide_number = $$props.slide_number);
	};

	return [favicon, title, description, slide_number];
}

class Component$b extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$b, null, safe_not_equal, {
			favicon: 0,
			title: 1,
			description: 2,
			slide_number: 3
		});
	}
}

/* generated by Svelte v3.59.1 */

function create_fragment$b(ctx) {
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
				description: "Фотостудія в Ужгороді",
				slide_number: "1"
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
				title: "Primo Skystudio",
				description: "Фотостудія в Ужгороді",
				slide_number: "1",
				links: [
					{
						"item": { "url": "/", "label": "Головна" }
					},
					{
						"item": { "url": "/fotozony", "label": "Фотозони" }
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

	component_2 = new Component$2({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "Primo Skystudio",
				description: "Фотостудія в Ужгороді",
				slide_number: "1"
			}
		});

	component_3 = new Component$3({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "Primo Skystudio",
				description: "Фотостудія в Ужгороді",
				slide_number: "1"
			}
		});

	component_4 = new Component$4({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "Primo Skystudio",
				description: "Фотостудія в Ужгороді",
				slide_number: "1",
				heading: "Переглянути&nbsp;фотозони",
				button: {
					"url": "/fotozony#mainContent",
					"label": "Переглянути"
				}
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
				title: "Primo Skystudio",
				description: "Фотостудія в Ужгороді",
				slide_number: "1",
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

	component_6 = new Component$7({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "Primo Skystudio",
				description: "Фотостудія в Ужгороді",
				slide_number: "1",
				heading: "Правила оренди студії",
				text: {
					"html": "<ol>\n<li>Оренда студії відбувається без передоплати. Будь ласка, про зміни попереджуйте заздалегідь.</li>\n<li>У студії є змінне взуття на 6 людей. Якщо людей буде більше, вам треба подбати про своє змінне взуття. У нас на підлозі коврове покриття, тому спокійно можна бути в шкарпетках.</li>\n<li>Якщо ви будете фотографуватись у взутті, воно обовʼязково має бути чистим!</li>\n<li>Вся студія бронюється за вами лише за умови роботи одного фотографа. Якщо працює два фотографа паралельно на різних зонах, оплата подвоюється.</li>\n<li>Чай, кава - безкоштовні. Капучино - за наявності молока :)</li>\n<li>В разі пошкодження майна вам необхідно повністю компенсувати збитки. Витрати оплачуються вами відразу. Шукаємо ринкову ціну пошкодженої речі при вас.</li>\n<li>Якщо ви плануєте зйомку з тваринами чи просто приходите з ними, попереджуйте про їх наявність завчасно та узгоджуйте це питання з нами.</li>\n<li>Відверті зйомки — це добре, але категорично заборонені зйомки порнографічного характеру.</li>\n</ol>\n<h3 id=\"skystudio\">Дякуємо за розуміння! З радістю чекаємо вас в Sky Studio.</h3>",
					"markdown": "1. Оренда студії відбувається без передоплати. Будь ласка, про зміни попереджуйте заздалегідь.\n2. У студії є змінне взуття на 6 людей. Якщо людей буде більше, вам треба подбати про своє змінне взуття. У нас на підлозі коврове покриття, тому спокійно можна бути в шкарпетках.\n3. Якщо ви будете фотографуватись у взутті, воно обовʼязково має бути чистим!\n4. Вся студія бронюється за вами лише за умови роботи одного фотографа. Якщо працює два фотографа паралельно на різних зонах, оплата подвоюється.\n5. Чай, кава - безкоштовні. Капучино - за наявності молока :)\n6. В разі пошкодження майна вам необхідно повністю компенсувати збитки. Витрати оплачуються вами відразу. Шукаємо ринкову ціну пошкодженої речі при вас.\n7. Якщо ви плануєте зйомку з тваринами чи просто приходите з ними, попереджуйте про їх наявність завчасно та узгоджуйте це питання з нами.\n8. Відверті зйомки — це добре, але категорично заборонені зйомки порнографічного характеру.\n\n### Дякуємо за розуміння! З радістю чекаємо вас в Sky Studio."
				}
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
				title: "Primo Skystudio",
				description: "Фотостудія в Ужгороді",
				slide_number: "1"
			}
		});

	component_8 = new Component$9({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "Primo Skystudio",
				description: "Фотостудія в Ужгороді",
				slide_number: "1"
			}
		});

	component_9 = new Component$a({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "Sky Studio – Фотостудія з крилами в Ужгороді",
				description: "Фотостудія в Ужгороді",
				slide_number: "1",
				email: "contact@skystudio.uz.ua",
				links: [
					{
						"item": { "url": "/", "label": "Головна" }
					},
					{
						"item": { "url": "/fotozony", "label": "Фотозони" }
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

	component_10 = new Component$b({
			props: {
				favicon: {
					"alt": "SkyStudio",
					"src": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"url": "https://taxobusmgaowcldvwgnr.supabase.co/storage/v1/object/public/images/f0456fff-45d0-494b-8ceb-d9904528bd86/1690717229271favicon.ico",
					"size": 4
				},
				title: "Primo Skystudio",
				description: "Фотостудія в Ужгороді",
				slide_number: "1"
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

class Component$c extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$b, safe_not_equal, {});
	}
}

export default Component$c;
