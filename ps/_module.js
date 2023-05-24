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

/* generated by Svelte v3.58.0 */

function create_fragment(ctx) {
	let meta;
	let link0;
	let link1;
	let style;
	let t;

	return {
		c() {
			meta = element("meta");
			link0 = element("link");
			link1 = element("link");
			style = element("style");
			t = text("@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n\nhtml {\n\n  /* Colors */\n/*   --color-accent: red;\n  --color-dark: #3E3D43;\n  --color-light: #FCFCFD;\n  --color-shade: #CBCACE;\n  --color-white: #FFF; */\n\n  /* Default property values */\n/*   --background: var(--color-shade);\n  --color: var(--color-dark);\n  --padding: 2rem;\n  --border: 1px solid var(--color-shade);\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2); \n  --border-radius: 8px;\n  --max-width: 1200px;\n  --border-color: var(--color-shade);\n  --transition-time: 0.1s;\n  --transition: var(--transition-time) color,\n    var(--transition-time) background-color,\n      var(--transition-time) border-color,\n        var(--transition-time) text-decoration-color,\n          var(--transition-time) box-shadow, var(--transtion-time) transform;\n */\n  /* Elements */\n/*   --heading-color: #252428;\n  --heading-font-size: 39px;\n  --heading-line-height: 48px;\n  --heading-font-weight: 700;\n\n  --subheading-color: #3E3D43;\n  --subheading-font-size: 1.5rem;\n\n  --button-color: white;\n  --button-background: var(--color-accent);\n  --button-border-radius: 4px;\n  --button-padding: 8px 20px; */\n\n    --color-accent: red;\n    --color-dark: #000000;\n    --color-dark-accent: #282A3A;\n    --color-light: #FCFCFD;\n    --color-shade: #282A3A;\n    --color-white: #000000;\n    --background: var(--color-shade);\n    --color: #C69749;\n    --padding: 2rem;\n    --border: 1px solid var(--color-shade);\n    --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n    --border-radius: 8px;\n    --max-width: 1200px;\n    --border-color: var(--color-shade);\n    --transition-time: 0.1s;\n    --transition: var(--transition-time) color, var(--transition-time) background-color, var(--transition-time) border-color, var(--transition-time) text-decoration-color, var(--transition-time) box-shadow, var(--transtion-time) transform;\n    --heading-color: #252428;\n    --heading-font-size: 39px;\n    --heading-line-height: 48px;\n    --heading-font-weight: 700;\n    --subheading-color: #3E3D43;\n    --subheading-font-size: 1.5rem;\n    --button-color: white;\n    --button-background: var(--color-accent);\n    --button-border-radius: 4px;\n    --button-padding: 8px 20px;\n\n}\n\n.dark-mode {\n  background: var(--color-dark);\n  color: var(--color-dark-accent);\n}\n\n.primo-page {\n  font-family: system-ui, sans-serif;\n  color: var(--color);\n  font-size: 1rem;\n  background: var(--background);\n}\n\n.primo-section .primo-content {\n  max-width: var(--max-width);\n  margin: 0 auto;\n  padding: var(--padding);\n  background: var(--color-white);\n}\n\n.primo-section .primo-content > * {\n    max-width: 700px;\n  }\n\n.primo-section .primo-content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.primo-section .primo-content p {\n    padding: 0.25rem 0;\n    line-height: 1.5;\n    font-size: 1rem;\n  }\n\n.primo-section .primo-content a {\n    text-decoration: underline;\n  }\n\n.primo-section .primo-content h1 {\n    font-size: 3.5rem;\n    font-weight: 600;\n    margin-bottom: 1rem;\n  }\n\n.primo-section .primo-content h2 {\n    font-size: 2.25rem;\n    font-weight: 600;\n    margin-bottom: 0.5rem;\n  }\n\n.primo-section .primo-content h3 {\n    font-size: 1.75rem; \n    font-weight: 600;\n    margin-bottom: 0.25rem;\n  }\n\n.primo-section .primo-content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n\n.primo-section .primo-content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n\n.primo-section .primo-content blockquote {\n    padding: 2rem;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.page-container {\n  max-width: var(--max-width, 1200px);\n  margin: 0 auto;\n  padding: 3rem var(--padding, 1rem); \n}\n\n.body {\n  font-size: var(--body-font-size);\n}\n\n.heading {\n  font-size: var(--heading-font-size, 49px);\n  line-height: var(--heading-line-height, 1);\n  font-weight: var(--heading-font-weight, 700);\n  color: var(--heading-color, #252428);\n}\n\n.button {\n  color: var(--color-white, white);\n  background: var(--color-accent, #154BF4);\n  border: 2px solid transparent;\n  border-radius: 5px;\n  padding: 8px 20px;\n  transition: var(--transition);\n}\n\n.button:hover {\n    box-shadow: 0 0 10px 5px rgba(0, 0, 0, 0.1);\n  }\n\n.button.inverted {\n    background: var(--color-white);\n    color: var(--color-accent);\n    border-color: var(--color-accent);\n  }");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-1b1szp7', document.head);
			meta = claim_element(head_nodes, "META", { name: true, content: true });
			link0 = claim_element(head_nodes, "LINK", { rel: true, href: true, type: true });
			link1 = claim_element(head_nodes, "LINK", { rel: true, href: true, type: true });
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t = claim_text(style_nodes, "@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n\nhtml {\n\n  /* Colors */\n/*   --color-accent: red;\n  --color-dark: #3E3D43;\n  --color-light: #FCFCFD;\n  --color-shade: #CBCACE;\n  --color-white: #FFF; */\n\n  /* Default property values */\n/*   --background: var(--color-shade);\n  --color: var(--color-dark);\n  --padding: 2rem;\n  --border: 1px solid var(--color-shade);\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2); \n  --border-radius: 8px;\n  --max-width: 1200px;\n  --border-color: var(--color-shade);\n  --transition-time: 0.1s;\n  --transition: var(--transition-time) color,\n    var(--transition-time) background-color,\n      var(--transition-time) border-color,\n        var(--transition-time) text-decoration-color,\n          var(--transition-time) box-shadow, var(--transtion-time) transform;\n */\n  /* Elements */\n/*   --heading-color: #252428;\n  --heading-font-size: 39px;\n  --heading-line-height: 48px;\n  --heading-font-weight: 700;\n\n  --subheading-color: #3E3D43;\n  --subheading-font-size: 1.5rem;\n\n  --button-color: white;\n  --button-background: var(--color-accent);\n  --button-border-radius: 4px;\n  --button-padding: 8px 20px; */\n\n    --color-accent: red;\n    --color-dark: #000000;\n    --color-dark-accent: #282A3A;\n    --color-light: #FCFCFD;\n    --color-shade: #282A3A;\n    --color-white: #000000;\n    --background: var(--color-shade);\n    --color: #C69749;\n    --padding: 2rem;\n    --border: 1px solid var(--color-shade);\n    --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n    --border-radius: 8px;\n    --max-width: 1200px;\n    --border-color: var(--color-shade);\n    --transition-time: 0.1s;\n    --transition: var(--transition-time) color, var(--transition-time) background-color, var(--transition-time) border-color, var(--transition-time) text-decoration-color, var(--transition-time) box-shadow, var(--transtion-time) transform;\n    --heading-color: #252428;\n    --heading-font-size: 39px;\n    --heading-line-height: 48px;\n    --heading-font-weight: 700;\n    --subheading-color: #3E3D43;\n    --subheading-font-size: 1.5rem;\n    --button-color: white;\n    --button-background: var(--color-accent);\n    --button-border-radius: 4px;\n    --button-padding: 8px 20px;\n\n}\n\n.dark-mode {\n  background: var(--color-dark);\n  color: var(--color-dark-accent);\n}\n\n.primo-page {\n  font-family: system-ui, sans-serif;\n  color: var(--color);\n  font-size: 1rem;\n  background: var(--background);\n}\n\n.primo-section .primo-content {\n  max-width: var(--max-width);\n  margin: 0 auto;\n  padding: var(--padding);\n  background: var(--color-white);\n}\n\n.primo-section .primo-content > * {\n    max-width: 700px;\n  }\n\n.primo-section .primo-content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.primo-section .primo-content p {\n    padding: 0.25rem 0;\n    line-height: 1.5;\n    font-size: 1rem;\n  }\n\n.primo-section .primo-content a {\n    text-decoration: underline;\n  }\n\n.primo-section .primo-content h1 {\n    font-size: 3.5rem;\n    font-weight: 600;\n    margin-bottom: 1rem;\n  }\n\n.primo-section .primo-content h2 {\n    font-size: 2.25rem;\n    font-weight: 600;\n    margin-bottom: 0.5rem;\n  }\n\n.primo-section .primo-content h3 {\n    font-size: 1.75rem; \n    font-weight: 600;\n    margin-bottom: 0.25rem;\n  }\n\n.primo-section .primo-content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n\n.primo-section .primo-content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n\n.primo-section .primo-content blockquote {\n    padding: 2rem;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.page-container {\n  max-width: var(--max-width, 1200px);\n  margin: 0 auto;\n  padding: 3rem var(--padding, 1rem); \n}\n\n.body {\n  font-size: var(--body-font-size);\n}\n\n.heading {\n  font-size: var(--heading-font-size, 49px);\n  line-height: var(--heading-line-height, 1);\n  font-weight: var(--heading-font-weight, 700);\n  color: var(--heading-color, #252428);\n}\n\n.button {\n  color: var(--color-white, white);\n  background: var(--color-accent, #154BF4);\n  border: 2px solid transparent;\n  border-radius: 5px;\n  padding: 8px 20px;\n  transition: var(--transition);\n}\n\n.button:hover {\n    box-shadow: 0 0 10px 5px rgba(0, 0, 0, 0.1);\n  }\n\n.button.inverted {\n    background: var(--color-white);\n    color: var(--color-accent);\n    border-color: var(--color-accent);\n  }");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(meta, "name", "viewport");
			attr(meta, "content", "width=device-width, initial-scale=1.0");
			attr(link0, "rel", "Shortcut Icon");
			attr(link0, "href", "http://web.archive.org/web/20200601010519im_/http://stars-egypt.org/wp-content/themes/organic_nonprofit/images/favicon.ico");
			attr(link0, "type", "image/x-icon");
			document.title = "Saint Andrew's Refugee Services";
			attr(link1, "rel", "Shortcut Icon");
			attr(link1, "href", "http://web.archive.org/web/20200601010519im_/http://stars-egypt.org/wp-content/themes/organic_nonprofit/images/favicon.ico");
			attr(link1, "type", "image/x-icon");
		},
		m(target, anchor) {
			append_hydration(document.head, meta);
			append_hydration(document.head, link0);
			append_hydration(document.head, link1);
			append_hydration(document.head, style);
			append_hydration(style, t);
		},
		p: noop,
		i: noop,
		o: noop,
		d(detaching) {
			detach(meta);
			detach(link0);
			detach(link1);
			detach(style);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { dow } = $$props;
	let { imeg } = $$props;
	let { link } = $$props;
	let { items } = $$props;

	$$self.$$set = $$props => {
		if ('dow' in $$props) $$invalidate(0, dow = $$props.dow);
		if ('imeg' in $$props) $$invalidate(1, imeg = $$props.imeg);
		if ('link' in $$props) $$invalidate(2, link = $$props.link);
		if ('items' in $$props) $$invalidate(3, items = $$props.items);
	};

	return [dow, imeg, link, items];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { dow: 0, imeg: 1, link: 2, items: 3 });
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i].link;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i].link;
	return child_ctx;
}

function get_each_context_2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[3] = list[i].link;
	return child_ctx;
}

// (264:6) {#each dow as {link}}
function create_each_block_2(ctx) {
	let li;
	let a;
	let t_value = /*link*/ ctx[3].label + "";
	let t;
	let a_href_value;

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
			a = claim_element(li_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[3].url);
			attr(a, "class", "svelte-124iln0");
			attr(li, "class", "svelte-124iln0");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, a);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*dow*/ 1 && t_value !== (t_value = /*link*/ ctx[3].label + "")) set_data(t, t_value);

			if (dirty & /*dow*/ 1 && a_href_value !== (a_href_value = /*link*/ ctx[3].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(li);
		}
	};
}

// (270:6) {#each items as {link}}
function create_each_block_1(ctx) {
	let a;
	let t_value = /*link*/ ctx[3].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[3].url);
			attr(a, "class", "nav svelte-124iln0");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*items*/ 4 && t_value !== (t_value = /*link*/ ctx[3].label + "")) set_data(t, t_value);

			if (dirty & /*items*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[3].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (281:8) {#each items as {link}}
function create_each_block(ctx) {
	let li;
	let a;
	let t_value = /*link*/ ctx[3].label + "";
	let t;
	let a_href_value;

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
			a = claim_element(li_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[3].url);
			attr(a, "class", "nav svelte-124iln0");
			attr(li, "class", "svelte-124iln0");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, a);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*items*/ 4 && t_value !== (t_value = /*link*/ ctx[3].label + "")) set_data(t, t_value);

			if (dirty & /*items*/ 4 && a_href_value !== (a_href_value = /*link*/ ctx[3].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(li);
		}
	};
}

function create_fragment$1(ctx) {
	let div5;
	let div4;
	let section;
	let a0;
	let t0_value = /*link*/ ctx[3].label + "";
	let t0;
	let t1;
	let img;
	let img_src_value;
	let a0_href_value;
	let t2;
	let div2;
	let div0;
	let a1;
	let t3;
	let t4;
	let ul0;
	let t5;
	let div1;
	let t6;
	let a2;
	let t7;
	let t8;
	let div3;
	let input0;
	let t9;
	let label0;
	let t10;
	let ul1;
	let t11;
	let li;
	let a3;
	let t12;
	let t13;
	let label1;
	let input1;
	let t14;
	let span;
	let mounted;
	let dispose;
	let each_value_2 = /*dow*/ ctx[0];
	let each_blocks_2 = [];

	for (let i = 0; i < each_value_2.length; i += 1) {
		each_blocks_2[i] = create_each_block_2(get_each_context_2(ctx, each_value_2, i));
	}

	let each_value_1 = /*items*/ ctx[2];
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks_1[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	let each_value = /*items*/ ctx[2];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	return {
		c() {
			div5 = element("div");
			div4 = element("div");
			section = element("section");
			a0 = element("a");
			t0 = text(t0_value);
			t1 = space();
			img = element("img");
			t2 = space();
			div2 = element("div");
			div0 = element("div");
			a1 = element("a");
			t3 = text("Services");
			t4 = space();
			ul0 = element("ul");

			for (let i = 0; i < each_blocks_2.length; i += 1) {
				each_blocks_2[i].c();
			}

			t5 = space();
			div1 = element("div");

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t6 = space();
			a2 = element("a");
			t7 = text("Facebook");
			t8 = space();
			div3 = element("div");
			input0 = element("input");
			t9 = space();
			label0 = element("label");
			t10 = space();
			ul1 = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t11 = space();
			li = element("li");
			a3 = element("a");
			t12 = text("Facebook");
			t13 = space();
			label1 = element("label");
			input1 = element("input");
			t14 = space();
			span = element("span");
			this.h();
		},
		l(nodes) {
			div5 = claim_element(nodes, "DIV", { class: true, id: true });
			var div5_nodes = children(div5);
			div4 = claim_element(div5_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			section = claim_element(div4_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			a0 = claim_element(section_nodes, "A", { href: true });
			var a0_nodes = children(a0);
			t0 = claim_text(a0_nodes, t0_value);
			t1 = claim_space(a0_nodes);
			img = claim_element(a0_nodes, "IMG", { class: true, src: true });
			a0_nodes.forEach(detach);
			t2 = claim_space(section_nodes);
			div2 = claim_element(section_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			div0 = claim_element(div2_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			a1 = claim_element(div0_nodes, "A", { href: true, class: true });
			var a1_nodes = children(a1);
			t3 = claim_text(a1_nodes, "Services");
			a1_nodes.forEach(detach);
			t4 = claim_space(div0_nodes);
			ul0 = claim_element(div0_nodes, "UL", { class: true });
			var ul0_nodes = children(ul0);

			for (let i = 0; i < each_blocks_2.length; i += 1) {
				each_blocks_2[i].l(ul0_nodes);
			}

			ul0_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t5 = claim_space(div2_nodes);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(div1_nodes);
			}

			t6 = claim_space(div1_nodes);
			a2 = claim_element(div1_nodes, "A", { href: true, class: true });
			var a2_nodes = children(a2);
			t7 = claim_text(a2_nodes, "Facebook");
			a2_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			t8 = claim_space(section_nodes);
			div3 = claim_element(section_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			input0 = claim_element(div3_nodes, "INPUT", { type: true, id: true });
			t9 = claim_space(div3_nodes);
			label0 = claim_element(div3_nodes, "LABEL", { for: true, class: true });
			var label0_nodes = children(label0);
			label0_nodes.forEach(detach);
			t10 = claim_space(div3_nodes);
			ul1 = claim_element(div3_nodes, "UL", { class: true });
			var ul1_nodes = children(ul1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul1_nodes);
			}

			t11 = claim_space(ul1_nodes);
			li = claim_element(ul1_nodes, "LI", { class: true });
			var li_nodes = children(li);
			a3 = claim_element(li_nodes, "A", { href: true, class: true });
			var a3_nodes = children(a3);
			t12 = claim_text(a3_nodes, "Facebook");
			a3_nodes.forEach(detach);
			li_nodes.forEach(detach);
			ul1_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			section_nodes.forEach(detach);
			t13 = claim_space(div4_nodes);
			label1 = claim_element(div4_nodes, "LABEL", { class: true });
			var label1_nodes = children(label1);
			input1 = claim_element(label1_nodes, "INPUT", { type: true, onchange: true, class: true });
			t14 = claim_space(label1_nodes);
			span = claim_element(label1_nodes, "SPAN", { class: true });
			children(span).forEach(detach);
			label1_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			div5_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(img, "class", "logo svelte-124iln0");
			if (!src_url_equal(img.src, img_src_value = /*imeg*/ ctx[1].url)) attr(img, "src", img_src_value);
			attr(a0, "href", a0_href_value = /*link*/ ctx[3].url);
			attr(a1, "href", "/");
			attr(a1, "class", "nav svelte-124iln0");
			attr(ul0, "class", "dropdown-menu svelte-124iln0");
			attr(div0, "class", "dropdown svelte-124iln0");
			attr(a2, "href", "https://www.facebook.com/standrewsrefugeeservices");
			attr(a2, "class", "fb svelte-124iln0");
			attr(div1, "class", "items svelte-124iln0");
			attr(div2, "class", "items svelte-124iln0");
			attr(input0, "type", "checkbox");
			attr(input0, "id", "menu-toggle-mobile");
			attr(label0, "for", "menu-toggle-mobile");
			attr(label0, "class", "toggle-label-mobile svelte-124iln0");
			attr(a3, "href", "https://www.facebook.com/standrewsrefugeeservices");
			attr(a3, "class", "fb svelte-124iln0");
			attr(li, "class", "svelte-124iln0");
			attr(ul1, "class", "dropdown-menu-mobile svelte-124iln0");
			attr(div3, "class", "items-mobile svelte-124iln0");
			attr(section, "class", "page-container svelte-124iln0");
			toggle_class(section, "dark-mode", /*isDarkMode*/ ctx[4]);
			attr(input1, "type", "checkbox");
			attr(input1, "onchange", /*toggleDarkMode*/ ctx[5]);
			attr(input1, "class", "svelte-124iln0");
			attr(span, "class", "slider round svelte-124iln0");
			attr(label1, "class", "switch svelte-124iln0");
			attr(div4, "class", "component");
			attr(div5, "class", "section");
			attr(div5, "id", "section-8c2e20fd-26f3-4f12-934a-73f6ebc111a3");
		},
		m(target, anchor) {
			insert_hydration(target, div5, anchor);
			append_hydration(div5, div4);
			append_hydration(div4, section);
			append_hydration(section, a0);
			append_hydration(a0, t0);
			append_hydration(a0, t1);
			append_hydration(a0, img);
			append_hydration(section, t2);
			append_hydration(section, div2);
			append_hydration(div2, div0);
			append_hydration(div0, a1);
			append_hydration(a1, t3);
			append_hydration(div0, t4);
			append_hydration(div0, ul0);

			for (let i = 0; i < each_blocks_2.length; i += 1) {
				if (each_blocks_2[i]) {
					each_blocks_2[i].m(ul0, null);
				}
			}

			append_hydration(div2, t5);
			append_hydration(div2, div1);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				if (each_blocks_1[i]) {
					each_blocks_1[i].m(div1, null);
				}
			}

			append_hydration(div1, t6);
			append_hydration(div1, a2);
			append_hydration(a2, t7);
			append_hydration(section, t8);
			append_hydration(section, div3);
			append_hydration(div3, input0);
			append_hydration(div3, t9);
			append_hydration(div3, label0);
			append_hydration(div3, t10);
			append_hydration(div3, ul1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul1, null);
				}
			}

			append_hydration(ul1, t11);
			append_hydration(ul1, li);
			append_hydration(li, a3);
			append_hydration(a3, t12);
			append_hydration(div4, t13);
			append_hydration(div4, label1);
			append_hydration(label1, input1);
			input1.checked = /*isDarkMode*/ ctx[4];
			append_hydration(label1, t14);
			append_hydration(label1, span);

			if (!mounted) {
				dispose = listen(input1, "change", /*input1_change_handler*/ ctx[6]);
				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*link*/ 8 && t0_value !== (t0_value = /*link*/ ctx[3].label + "")) set_data(t0, t0_value);

			if (dirty & /*imeg*/ 2 && !src_url_equal(img.src, img_src_value = /*imeg*/ ctx[1].url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*link*/ 8 && a0_href_value !== (a0_href_value = /*link*/ ctx[3].url)) {
				attr(a0, "href", a0_href_value);
			}

			if (dirty & /*dow*/ 1) {
				each_value_2 = /*dow*/ ctx[0];
				let i;

				for (i = 0; i < each_value_2.length; i += 1) {
					const child_ctx = get_each_context_2(ctx, each_value_2, i);

					if (each_blocks_2[i]) {
						each_blocks_2[i].p(child_ctx, dirty);
					} else {
						each_blocks_2[i] = create_each_block_2(child_ctx);
						each_blocks_2[i].c();
						each_blocks_2[i].m(ul0, null);
					}
				}

				for (; i < each_blocks_2.length; i += 1) {
					each_blocks_2[i].d(1);
				}

				each_blocks_2.length = each_value_2.length;
			}

			if (dirty & /*items*/ 4) {
				each_value_1 = /*items*/ ctx[2];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks_1[i]) {
						each_blocks_1[i].p(child_ctx, dirty);
					} else {
						each_blocks_1[i] = create_each_block_1(child_ctx);
						each_blocks_1[i].c();
						each_blocks_1[i].m(div1, t6);
					}
				}

				for (; i < each_blocks_1.length; i += 1) {
					each_blocks_1[i].d(1);
				}

				each_blocks_1.length = each_value_1.length;
			}

			if (dirty & /*items*/ 4) {
				each_value = /*items*/ ctx[2];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(ul1, t11);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}

			if (dirty & /*isDarkMode*/ 16) {
				toggle_class(section, "dark-mode", /*isDarkMode*/ ctx[4]);
			}

			if (dirty & /*isDarkMode*/ 16) {
				input1.checked = /*isDarkMode*/ ctx[4];
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div5);
			destroy_each(each_blocks_2, detaching);
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
			mounted = false;
			dispose();
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	let { dow } = $$props;
	let { imeg } = $$props;
	let { link } = $$props;
	let { items } = $$props;

	// import {fade} from 'svelte/transition'
	// import Icon from '@iconify/svelte/dist/Icon.svelte'
	// let mobileNavOpen = false 
	// function toggleMobileNav() {
	//   mobileNavOpen = !mobileNavOpen
	// }
	let isDarkMode = false;

	function toggleDarkMode() {
		$$invalidate(4, isDarkMode = !isDarkMode);
	}

	function input1_change_handler() {
		isDarkMode = this.checked;
		$$invalidate(4, isDarkMode);
	}

	$$self.$$set = $$props => {
		if ('dow' in $$props) $$invalidate(0, dow = $$props.dow);
		if ('imeg' in $$props) $$invalidate(1, imeg = $$props.imeg);
		if ('link' in $$props) $$invalidate(3, link = $$props.link);
		if ('items' in $$props) $$invalidate(2, items = $$props.items);
	};

	return [dow, imeg, items, link, isDarkMode, toggleDarkMode, input1_change_handler];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, { dow: 0, imeg: 1, link: 3, items: 2 });
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

/* generated by Svelte v3.58.0 */

function create_if_block_1(ctx) {
	let div;
	let previous_key = /*activeIndex*/ ctx[1];
	let key_block = create_key_block(ctx);

	return {
		c() {
			div = element("div");
			key_block.c();
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			key_block.l(div_nodes);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "card svelte-15xaj3j");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			key_block.m(div, null);
		},
		p(ctx, dirty) {
			if (dirty & /*activeIndex*/ 2 && safe_not_equal(previous_key, previous_key = /*activeIndex*/ ctx[1])) {
				group_outros();
				transition_out(key_block, 1, 1, noop);
				check_outros();
				key_block = create_key_block(ctx);
				key_block.c();
				transition_in(key_block, 1);
				key_block.m(div, null);
			} else {
				key_block.p(ctx, dirty);
			}
		},
		i(local) {
			transition_in(key_block);
		},
		o(local) {
			transition_out(key_block);
		},
		d(detaching) {
			if (detaching) detach(div);
			key_block.d(detaching);
		}
	};
}

// (132:3) {#key activeIndex}
function create_key_block(ctx) {
	let img;
	let img_src_value;
	let img_intro;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { src: true, class: true });
			this.h();
		},
		h() {
			if (!src_url_equal(img.src, img_src_value = /*activeItem*/ ctx[3].images.url)) attr(img, "src", img_src_value);
			attr(img, "class", "svelte-15xaj3j");
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*activeItem*/ 8 && !src_url_equal(img.src, img_src_value = /*activeItem*/ ctx[3].images.url)) {
				attr(img, "src", img_src_value);
			}
		},
		i(local) {
			if (!img_intro) {
				add_render_callback(() => {
					img_intro = create_in_transition(img, fade, { duration: 10 });
					img_intro.start();
				});
			}
		},
		o: noop,
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (137:4) {#if testimonials.length > 1}
function create_if_block(ctx) {
	let div;
	let button0;
	let svg0;
	let path0;
	let button0_disabled_value;
	let t;
	let button1;
	let svg1;
	let path1;
	let button1_disabled_value;
	let mounted;
	let dispose;

	return {
		c() {
			div = element("div");
			button0 = element("button");
			svg0 = svg_element("svg");
			path0 = svg_element("path");
			t = space();
			button1 = element("button");
			svg1 = svg_element("svg");
			path1 = svg_element("path");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			button0 = claim_element(div_nodes, "BUTTON", { "aria-label": true, class: true });
			var button0_nodes = children(button0);

			svg0 = claim_svg_element(button0_nodes, "svg", {
				viewBox: true,
				fill: true,
				xmlns: true,
				class: true
			});

			var svg0_nodes = children(svg0);
			path0 = claim_svg_element(svg0_nodes, "path", { d: true, fill: true });
			children(path0).forEach(detach);
			svg0_nodes.forEach(detach);
			button0_nodes.forEach(detach);
			t = claim_space(div_nodes);
			button1 = claim_element(div_nodes, "BUTTON", { "aria-label": true, class: true });
			var button1_nodes = children(button1);

			svg1 = claim_svg_element(button1_nodes, "svg", {
				viewBox: true,
				fill: true,
				xmlns: true,
				class: true
			});

			var svg1_nodes = children(svg1);
			path1 = claim_svg_element(svg1_nodes, "path", { d: true, fill: true });
			children(path1).forEach(detach);
			svg1_nodes.forEach(detach);
			button1_nodes.forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(path0, "d", "M0.375 12C0.375 18.4219 5.57812 23.625 12 23.625C18.4219 23.625 23.625 18.4219 23.625 12C23.625 5.57812 18.4219 0.375 12 0.375C5.57812 0.375 0.375 5.57812 0.375 12ZM12 1.875C17.5641 1.875 22.125 6.37969 22.125 12C22.125 17.5641 17.6203 22.125 12 22.125C6.43594 22.125 1.875 17.6203 1.875 12C1.875 6.43594 6.37969 1.875 12 1.875ZM16.0594 12.3984L10.6641 17.7891C10.4438 18.0094 10.0875 18.0094 9.86719 17.7891L9.53437 17.4562C9.31406 17.2359 9.31406 16.8797 9.53437 16.6594L14.2031 12L9.53906 7.33594C9.31875 7.11562 9.31875 6.75938 9.53906 6.53906L9.87188 6.20625C10.0922 5.98594 10.4484 5.98594 10.6688 6.20625L16.0641 11.5969C16.2797 11.8219 16.2797 12.1781 16.0594 12.3984Z");
			attr(path0, "fill", "#252428");
			attr(svg0, "viewBox", "0 0 24 24");
			attr(svg0, "fill", "none");
			attr(svg0, "xmlns", "http://www.w3.org/2000/svg");
			attr(svg0, "class", "svelte-15xaj3j");
			button0.disabled = button0_disabled_value = /*activeIndex*/ ctx[1] === 0;
			attr(button0, "aria-label", "Show previous item");
			attr(button0, "class", "svelte-15xaj3j");
			attr(path1, "d", "M0.375 12C0.375 18.4219 5.57812 23.625 12 23.625C18.4219 23.625 23.625 18.4219 23.625 12C23.625 5.57812 18.4219 0.375 12 0.375C5.57812 0.375 0.375 5.57812 0.375 12ZM12 1.875C17.5641 1.875 22.125 6.37969 22.125 12C22.125 17.5641 17.6203 22.125 12 22.125C6.43594 22.125 1.875 17.6203 1.875 12C1.875 6.43594 6.37969 1.875 12 1.875ZM16.0594 12.3984L10.6641 17.7891C10.4438 18.0094 10.0875 18.0094 9.86719 17.7891L9.53437 17.4562C9.31406 17.2359 9.31406 16.8797 9.53437 16.6594L14.2031 12L9.53906 7.33594C9.31875 7.11562 9.31875 6.75938 9.53906 6.53906L9.87188 6.20625C10.0922 5.98594 10.4484 5.98594 10.6688 6.20625L16.0641 11.5969C16.2797 11.8219 16.2797 12.1781 16.0594 12.3984Z");
			attr(path1, "fill", "#252428");
			attr(svg1, "viewBox", "0 0 24 24");
			attr(svg1, "fill", "none");
			attr(svg1, "xmlns", "http://www.w3.org/2000/svg");
			attr(svg1, "class", "svelte-15xaj3j");
			button1.disabled = button1_disabled_value = /*activeIndex*/ ctx[1] >= /*testimonials*/ ctx[0].length - 1;
			attr(button1, "aria-label", "Show next item");
			attr(button1, "class", "svelte-15xaj3j");
			attr(div, "class", "controls svelte-15xaj3j");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, button0);
			append_hydration(button0, svg0);
			append_hydration(svg0, path0);
			append_hydration(div, t);
			append_hydration(div, button1);
			append_hydration(button1, svg1);
			append_hydration(svg1, path1);

			if (!mounted) {
				dispose = [
					listen(button0, "click", /*click_handler*/ ctx[12]),
					listen(button1, "click", /*click_handler_1*/ ctx[13])
				];

				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*activeIndex*/ 2 && button0_disabled_value !== (button0_disabled_value = /*activeIndex*/ ctx[1] === 0)) {
				button0.disabled = button0_disabled_value;
			}

			if (dirty & /*activeIndex, testimonials*/ 3 && button1_disabled_value !== (button1_disabled_value = /*activeIndex*/ ctx[1] >= /*testimonials*/ ctx[0].length - 1)) {
				button1.disabled = button1_disabled_value;
			}
		},
		d(detaching) {
			if (detaching) detach(div);
			mounted = false;
			run_all(dispose);
		}
	};
}

function create_fragment$2(ctx) {
	let div2;
	let div1;
	let aside;
	let div0;
	let t;
	let if_block0 = /*activeItem*/ ctx[3].images.url && create_if_block_1(ctx);
	let if_block1 = /*testimonials*/ ctx[0].length > 1 && create_if_block(ctx);

	return {
		c() {
			div2 = element("div");
			div1 = element("div");
			aside = element("aside");
			div0 = element("div");
			if (if_block0) if_block0.c();
			t = space();
			if (if_block1) if_block1.c();
			this.h();
		},
		l(nodes) {
			div2 = claim_element(nodes, "DIV", { class: true, id: true });
			var div2_nodes = children(div2);
			div1 = claim_element(div2_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			aside = claim_element(div1_nodes, "ASIDE", { class: true });
			var aside_nodes = children(aside);
			div0 = claim_element(aside_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			if (if_block0) if_block0.l(div0_nodes);
			t = claim_space(div0_nodes);
			if (if_block1) if_block1.l(div0_nodes);
			div0_nodes.forEach(detach);
			aside_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			div2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "testimonial svelte-15xaj3j");
			attr(aside, "class", "page-container svelte-15xaj3j");
			attr(div1, "class", "component");
			attr(div2, "class", "section");
			attr(div2, "id", "section-f876faa7-2063-494a-ba57-0842263bc5a9");
		},
		m(target, anchor) {
			insert_hydration(target, div2, anchor);
			append_hydration(div2, div1);
			append_hydration(div1, aside);
			append_hydration(aside, div0);
			if (if_block0) if_block0.m(div0, null);
			append_hydration(div0, t);
			if (if_block1) if_block1.m(div0, null);
		},
		p(ctx, [dirty]) {
			if (/*activeItem*/ ctx[3].images.url) {
				if (if_block0) {
					if_block0.p(ctx, dirty);

					if (dirty & /*activeItem*/ 8) {
						transition_in(if_block0, 1);
					}
				} else {
					if_block0 = create_if_block_1(ctx);
					if_block0.c();
					transition_in(if_block0, 1);
					if_block0.m(div0, t);
				}
			} else if (if_block0) {
				if_block0.d(1);
				if_block0 = null;
			}

			if (/*testimonials*/ ctx[0].length > 1) {
				if (if_block1) {
					if_block1.p(ctx, dirty);
				} else {
					if_block1 = create_if_block(ctx);
					if_block1.c();
					if_block1.m(div0, null);
				}
			} else if (if_block1) {
				if_block1.d(1);
				if_block1 = null;
			}
		},
		i(local) {
			transition_in(if_block0);
		},
		o: noop,
		d(detaching) {
			if (detaching) detach(div2);
			if (if_block0) if_block0.d();
			if (if_block1) if_block1.d();
		}
	};
}

function instance$2($$self, $$props, $$invalidate) {
	let activeItem;
	let isOnLastSlide;
	let { dow } = $$props;
	let { imeg } = $$props;
	let { link } = $$props;
	let { items } = $$props;
	let { next_slide_time } = $$props;
	let { testimonials } = $$props;
	let activeIndex = 0;

	function showPreviousItem() {
		$$invalidate(1, activeIndex = activeIndex - 1);
	}

	function showNextItem() {
		$$invalidate(1, activeIndex = activeIndex + 1);
	}

	let interval;

	function createInterval() {
		if (interval) clearInterval(interval);
		if (!next_slide_time) return;

		$$invalidate(11, interval = setInterval(
			() => {
				if (isOnLastSlide) {
					showItem(0);
				} else showNextItem();
			},
			next_slide_time * 1000
		));
	}

	let autoSlideEnabled = true;

	function showItem(i) {
		$$invalidate(1, activeIndex = i);
	}

	const click_handler = () => {
		$$invalidate(2, autoSlideEnabled = false);
		showPreviousItem();
	};

	const click_handler_1 = () => {
		$$invalidate(2, autoSlideEnabled = false);
		showNextItem();
	};

	$$self.$$set = $$props => {
		if ('dow' in $$props) $$invalidate(6, dow = $$props.dow);
		if ('imeg' in $$props) $$invalidate(7, imeg = $$props.imeg);
		if ('link' in $$props) $$invalidate(8, link = $$props.link);
		if ('items' in $$props) $$invalidate(9, items = $$props.items);
		if ('next_slide_time' in $$props) $$invalidate(10, next_slide_time = $$props.next_slide_time);
		if ('testimonials' in $$props) $$invalidate(0, testimonials = $$props.testimonials);
	};

	$$self.$$.update = () => {
		if ($$self.$$.dirty & /*testimonials, activeIndex*/ 3) {
			 $$invalidate(3, activeItem = testimonials[activeIndex]);
		}

		if ($$self.$$.dirty & /*activeIndex, testimonials*/ 3) {
			 isOnLastSlide = activeIndex === testimonials.length - 1;
		}

		if ($$self.$$.dirty & /*autoSlideEnabled, interval*/ 2052) {
			 if (!autoSlideEnabled) {
				clearInterval(interval);
			}
		}

		if ($$self.$$.dirty & /*next_slide_time*/ 1024) {
			 (createInterval());
		}
	};

	return [
		testimonials,
		activeIndex,
		autoSlideEnabled,
		activeItem,
		showPreviousItem,
		showNextItem,
		dow,
		imeg,
		link,
		items,
		next_slide_time,
		interval,
		click_handler,
		click_handler_1
	];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$2, safe_not_equal, {
			dow: 6,
			imeg: 7,
			link: 8,
			items: 9,
			next_slide_time: 10,
			testimonials: 0
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[4] = list[i];
	return child_ctx;
}

function get_each_context_1$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[7] = list[i];
	return child_ctx;
}

function get_each_context_2$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[10] = list[i];
	return child_ctx;
}

function get_each_context_3(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[13] = list[i];
	return child_ctx;
}

function get_each_context_4(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[16] = list[i];
	return child_ctx;
}

// (58:2) {#if heder.heading}
function create_if_block_2(ctx) {
	let h1;
	let t_value = /*heder*/ ctx[16].heading + "";
	let t;

	return {
		c() {
			h1 = element("h1");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			h1 = claim_element(nodes, "H1", { class: true });
			var h1_nodes = children(h1);
			t = claim_text(h1_nodes, t_value);
			h1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h1, "class", "svelte-1xfk3p6");
		},
		m(target, anchor) {
			insert_hydration(target, h1, anchor);
			append_hydration(h1, t);
		},
		p(ctx, dirty) {
			if (dirty & /*items*/ 1 && t_value !== (t_value = /*heder*/ ctx[16].heading + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(h1);
		}
	};
}

// (56:2) {#each hed.header as heder}
function create_each_block_4(ctx) {
	let if_block_anchor;
	let if_block = /*heder*/ ctx[16].heading && create_if_block_2(ctx);

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
		p(ctx, dirty) {
			if (/*heder*/ ctx[16].heading) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block_2(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (65:2) {#if item.subhed}
function create_if_block_1$1(ctx) {
	let span;
	let t_value = /*item*/ ctx[13].subhed + "";
	let t;

	return {
		c() {
			span = element("span");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t = claim_text(span_nodes, t_value);
			span_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "subhed svelte-1xfk3p6");
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
			append_hydration(span, t);
		},
		p(ctx, dirty) {
			if (dirty & /*items*/ 1 && t_value !== (t_value = /*item*/ ctx[13].subhed + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (63:2) {#each hed.items as item}
function create_each_block_3(ctx) {
	let if_block_anchor;
	let if_block = /*item*/ ctx[13].subhed && create_if_block_1$1(ctx);

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
		p(ctx, dirty) {
			if (/*item*/ ctx[13].subhed) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block_1$1(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (70:8) {#each hed.texter as text}
function create_each_block_2$1(ctx) {
	let p;
	let t_value = /*text*/ ctx[10].pos + "";
	let t;

	return {
		c() {
			p = element("p");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			p = claim_element(nodes, "P", { class: true });
			var p_nodes = children(p);
			t = claim_text(p_nodes, t_value);
			p_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(p, "class", "svelte-1xfk3p6");
		},
		m(target, anchor) {
			insert_hydration(target, p, anchor);
			append_hydration(p, t);
		},
		p(ctx, dirty) {
			if (dirty & /*items*/ 1 && t_value !== (t_value = /*text*/ ctx[10].pos + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(p);
		}
	};
}

// (75:6) {#if list.ls}
function create_if_block$1(ctx) {
	let li;
	let t_value = /*list*/ ctx[7].ls + "";
	let t;

	return {
		c() {
			li = element("li");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", { class: true });
			var li_nodes = children(li);
			t = claim_text(li_nodes, t_value);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(li, "class", "svelte-1xfk3p6");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, t);
		},
		p(ctx, dirty) {
			if (dirty & /*items*/ 1 && t_value !== (t_value = /*list*/ ctx[7].ls + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(li);
		}
	};
}

// (74:8) {#each hed.lists as list}
function create_each_block_1$1(ctx) {
	let if_block_anchor;
	let if_block = /*list*/ ctx[7].ls && create_if_block$1(ctx);

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
		p(ctx, dirty) {
			if (/*list*/ ctx[7].ls) {
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
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (54:2) {#each items as hed}
function create_each_block$1(ctx) {
	let div1;
	let t0;
	let t1;
	let div0;
	let t2;
	let ul;
	let t3;
	let each_value_4 = /*hed*/ ctx[4].header;
	let each_blocks_3 = [];

	for (let i = 0; i < each_value_4.length; i += 1) {
		each_blocks_3[i] = create_each_block_4(get_each_context_4(ctx, each_value_4, i));
	}

	let each_value_3 = /*hed*/ ctx[4].items;
	let each_blocks_2 = [];

	for (let i = 0; i < each_value_3.length; i += 1) {
		each_blocks_2[i] = create_each_block_3(get_each_context_3(ctx, each_value_3, i));
	}

	let each_value_2 = /*hed*/ ctx[4].texter;
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_2.length; i += 1) {
		each_blocks_1[i] = create_each_block_2$1(get_each_context_2$1(ctx, each_value_2, i));
	}

	let each_value_1 = /*hed*/ ctx[4].lists;
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1$1(get_each_context_1$1(ctx, each_value_1, i));
	}

	return {
		c() {
			div1 = element("div");

			for (let i = 0; i < each_blocks_3.length; i += 1) {
				each_blocks_3[i].c();
			}

			t0 = space();

			for (let i = 0; i < each_blocks_2.length; i += 1) {
				each_blocks_2[i].c();
			}

			t1 = space();
			div0 = element("div");

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].c();
			}

			t2 = space();
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t3 = space();
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true });
			var div1_nodes = children(div1);

			for (let i = 0; i < each_blocks_3.length; i += 1) {
				each_blocks_3[i].l(div1_nodes);
			}

			t0 = claim_space(div1_nodes);

			for (let i = 0; i < each_blocks_2.length; i += 1) {
				each_blocks_2[i].l(div1_nodes);
			}

			t1 = claim_space(div1_nodes);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				each_blocks_1[i].l(div0_nodes);
			}

			t2 = claim_space(div0_nodes);
			ul = claim_element(div0_nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(ul, "class", "svelte-1xfk3p6");
			attr(div0, "class", "text");
			attr(div1, "class", "content svelte-1xfk3p6");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);

			for (let i = 0; i < each_blocks_3.length; i += 1) {
				if (each_blocks_3[i]) {
					each_blocks_3[i].m(div1, null);
				}
			}

			append_hydration(div1, t0);

			for (let i = 0; i < each_blocks_2.length; i += 1) {
				if (each_blocks_2[i]) {
					each_blocks_2[i].m(div1, null);
				}
			}

			append_hydration(div1, t1);
			append_hydration(div1, div0);

			for (let i = 0; i < each_blocks_1.length; i += 1) {
				if (each_blocks_1[i]) {
					each_blocks_1[i].m(div0, null);
				}
			}

			append_hydration(div0, t2);
			append_hydration(div0, ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}

			append_hydration(div1, t3);
		},
		p(ctx, dirty) {
			if (dirty & /*items*/ 1) {
				each_value_4 = /*hed*/ ctx[4].header;
				let i;

				for (i = 0; i < each_value_4.length; i += 1) {
					const child_ctx = get_each_context_4(ctx, each_value_4, i);

					if (each_blocks_3[i]) {
						each_blocks_3[i].p(child_ctx, dirty);
					} else {
						each_blocks_3[i] = create_each_block_4(child_ctx);
						each_blocks_3[i].c();
						each_blocks_3[i].m(div1, t0);
					}
				}

				for (; i < each_blocks_3.length; i += 1) {
					each_blocks_3[i].d(1);
				}

				each_blocks_3.length = each_value_4.length;
			}

			if (dirty & /*items*/ 1) {
				each_value_3 = /*hed*/ ctx[4].items;
				let i;

				for (i = 0; i < each_value_3.length; i += 1) {
					const child_ctx = get_each_context_3(ctx, each_value_3, i);

					if (each_blocks_2[i]) {
						each_blocks_2[i].p(child_ctx, dirty);
					} else {
						each_blocks_2[i] = create_each_block_3(child_ctx);
						each_blocks_2[i].c();
						each_blocks_2[i].m(div1, t1);
					}
				}

				for (; i < each_blocks_2.length; i += 1) {
					each_blocks_2[i].d(1);
				}

				each_blocks_2.length = each_value_3.length;
			}

			if (dirty & /*items*/ 1) {
				each_value_2 = /*hed*/ ctx[4].texter;
				let i;

				for (i = 0; i < each_value_2.length; i += 1) {
					const child_ctx = get_each_context_2$1(ctx, each_value_2, i);

					if (each_blocks_1[i]) {
						each_blocks_1[i].p(child_ctx, dirty);
					} else {
						each_blocks_1[i] = create_each_block_2$1(child_ctx);
						each_blocks_1[i].c();
						each_blocks_1[i].m(div0, t2);
					}
				}

				for (; i < each_blocks_1.length; i += 1) {
					each_blocks_1[i].d(1);
				}

				each_blocks_1.length = each_value_2.length;
			}

			if (dirty & /*items*/ 1) {
				each_value_1 = /*hed*/ ctx[4].lists;
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1$1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1$1(child_ctx);
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
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks_3, detaching);
			destroy_each(each_blocks_2, detaching);
			destroy_each(each_blocks_1, detaching);
			destroy_each(each_blocks, detaching);
		}
	};
}

function create_fragment$3(ctx) {
	let div1;
	let div0;
	let section;
	let each_value = /*items*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			section = element("section");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			section = claim_element(div0_nodes, "SECTION", { class: true });
			var section_nodes = children(section);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(section_nodes);
			}

			section_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(section, "class", "page-container svelte-1xfk3p6");
			attr(div0, "class", "component");
			attr(div1, "class", "section");
			attr(div1, "id", "section-1aabe75e-67a9-4da3-b17b-9e2850736b77");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			append_hydration(div0, section);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(section, null);
				}
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*items*/ 1) {
				each_value = /*items*/ ctx[0];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(section, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks, detaching);
		}
	};
}

function instance$3($$self, $$props, $$invalidate) {
	let { dow } = $$props;
	let { imeg } = $$props;
	let { link } = $$props;
	let { items } = $$props;

	$$self.$$set = $$props => {
		if ('dow' in $$props) $$invalidate(1, dow = $$props.dow);
		if ('imeg' in $$props) $$invalidate(2, imeg = $$props.imeg);
		if ('link' in $$props) $$invalidate(3, link = $$props.link);
		if ('items' in $$props) $$invalidate(0, items = $$props.items);
	};

	return [items, dow, imeg, link];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$3, create_fragment$3, safe_not_equal, { dow: 1, imeg: 2, link: 3, items: 0 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$4(ctx) {
	let div1;
	let div0;
	let footer;
	let p;
	let t;

	return {
		c() {
			div1 = element("div");
			div0 = element("div");
			footer = element("footer");
			p = element("p");
			t = text("Copyright © 2022 · All Rights Reserved · St. Andrew's Refugee Services");
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			div0 = claim_element(div1_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			footer = claim_element(div0_nodes, "FOOTER", { class: true });
			var footer_nodes = children(footer);
			p = claim_element(footer_nodes, "P", {});
			var p_nodes = children(p);
			t = claim_text(p_nodes, "Copyright © 2022 · All Rights Reserved · St. Andrew's Refugee Services");
			p_nodes.forEach(detach);
			footer_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(footer, "class", "page-container svelte-yvf7nk");
			attr(div0, "class", "component");
			attr(div1, "class", "section");
			attr(div1, "id", "section-cd5144a5-75a9-4767-81e5-dccfc8324f88");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, div0);
			append_hydration(div0, footer);
			append_hydration(footer, p);
			append_hydration(p, t);
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
	let { dow } = $$props;
	let { imeg } = $$props;
	let { link } = $$props;
	let { items } = $$props;

	$$self.$$set = $$props => {
		if ('dow' in $$props) $$invalidate(0, dow = $$props.dow);
		if ('imeg' in $$props) $$invalidate(1, imeg = $$props.imeg);
		if ('link' in $$props) $$invalidate(2, link = $$props.link);
		if ('items' in $$props) $$invalidate(3, items = $$props.items);
	};

	return [dow, imeg, link, items];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$4, create_fragment$4, safe_not_equal, { dow: 0, imeg: 1, link: 2, items: 3 });
	}
}

/* generated by Svelte v3.58.0 */

function instance$5($$self, $$props, $$invalidate) {
	let { dow } = $$props;
	let { imeg } = $$props;
	let { link } = $$props;
	let { items } = $$props;

	$$self.$$set = $$props => {
		if ('dow' in $$props) $$invalidate(0, dow = $$props.dow);
		if ('imeg' in $$props) $$invalidate(1, imeg = $$props.imeg);
		if ('link' in $$props) $$invalidate(2, link = $$props.link);
		if ('items' in $$props) $$invalidate(3, items = $$props.items);
	};

	return [dow, imeg, link, items];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$5, null, safe_not_equal, { dow: 0, imeg: 1, link: 2, items: 3 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$5(ctx) {
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
	let current;

	component_0 = new Component({
			props: {
				dow: [
					{
						"link": {
							"url": "/rlap",
							"label": "Refugee Legal Aid Program"
						}
					},
					{
						"link": {
							"url": "/ucyd",
							"label": "Unaccompanied Children and Youth Department"
						}
					},
					{
						"link": {
							"url": "/cod",
							"label": "Community Outreach Services"
						}
					},
					{
						"link": {
							"url": "/ps",
							"label": "Psychosocial Services Services"
						}
					},
					{
						"link": {
							"url": "/education",
							"label": "Education Services"
						}
					}
				],
				imeg: {
					"alt": "",
					"src": "https://i.imgur.com/XbRkfNe.png",
					"url": "https://i.imgur.com/XbRkfNe.png",
					"size": null
				},
				link: { "url": "/", "label": "" },
				items: [
					{
						"link": {
							"url": "/contact",
							"label": "Contact",
							"active": false
						}
					},
					{
						"link": {
							"url": "/donate",
							"label": "Donate",
							"active": false
						}
					},
					{
						"link": {
							"url": "/get-involved",
							"label": "Get-Involved"
						}
					}
				]
			}
		});

	component_1 = new Component$1({
			props: {
				dow: [
					{
						"link": {
							"url": "/rlap",
							"label": "Refugee Legal Aid Program"
						}
					},
					{
						"link": {
							"url": "/ucyd",
							"label": "Unaccompanied Children and Youth Department"
						}
					},
					{
						"link": {
							"url": "/cod",
							"label": "Community Outreach Services"
						}
					},
					{
						"link": {
							"url": "/ps",
							"label": "Psychosocial Services Services"
						}
					},
					{
						"link": {
							"url": "/education",
							"label": "Education Services"
						}
					}
				],
				imeg: {
					"alt": "",
					"src": "data:image/png;base64,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",
					"url": "data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAATwAAADmCAMAAAB/CcnJAAACN1BMVEUAAAAAAADZABvdABvUAADXAAvZABPWAAYBAQETERGAgIAnGxsKCgoEBAQkISEHBgbUqqr///9EQUEYFxaHh4cQDw9QS0s0MjITDw89OzqGf38EAwRrZ2XeHC6Ee3sbGRg1MTG/v7+UkY9iYF5NSkoqJiY5MjJra17bCx4CAQElIyM9Ozs8NDQqKipZTU0/OjpmMzNtaGV7e3sGBgbYxLFBPj0XFRVSUFCjnJxPS0snJSXMzMxUUlBaVlYTDw8zLi53d3INCgpdVVUFBQUyLi4vKirhLj1qZWUPDg5lYGDeJi0LCQnjPktTUU6urq5KSUe/v788OTlyb22hl5ceHBvgOD19enowMDAcFhZCPz9aVlYvKykmJSV3dHRLREQaFxcJBQUDAwMjHBxSTk4XFhfwnZ+OioofHh7cGSHx1NToaWIaFhZMSkoaGBhgXVooJydzcG0sKipcXFznYGjzvrjaEB2Kh4deWlpDOjoDAwMCAgIRDQ16dnbxo47kU1Tuj4hLSkpeXFz2qqEXFRWBenrvl40FBQUjHh7ypozzqaWiop9KRETqdWlRTEpvbGzuiY63t7c+Pj3sgHDocW7qeXbjQkzvz8frhYJiYGBoZGTBwcHlTlPgJDVcWVbdEygNCgrtkn/ukIjren45NzYhHR3hMj50cnLoZmZDOzuoo6OGhITnV2TiRUPyvLwxMDCdmprqbXdpZmbkTFfmXF7hSUUjICAzLy9bWFjnW1YPDg6Sj4+GhIRGREQz3pKRAAAAvXRSTlMA//////////7nBhby/LTjBgGX3BHaMbmJiya1SN48z6kENmWHoEcT8/DKsEAMKGYFWxulDXjEliQ9wwp2i0SaL04h+IBWyjruMMRot2ITkBycZRujsF7DLqdHjtlNS7qQWySA/FhG1tUSZ3+i5VKrVLgZkSvlU4I1yXqacySCSblyG21FMTZlFEFSU1VrcWo5xEJvY6UgWJeHKZrUWenLKjx123u9hHpbL3ChnDnQRIV6rIWJkXirc/9igfI9fA6cAAAo1klEQVR4nO1diV8VVftnaO4K9162S15iR2RTQRQQl0QFQRJxATdUCn1zSxDLsjIlcyu1ci8V01dN316zesuy9/f+cb/nzNlnH7ylcP1+9APMnTlz7nfOOc96nkmbErh28Xn3YBLjR//e592FSYxV6tHn3YXJi6sBtfv48+7EpMUqVa0+9rw7MVnxnur3BR48715MVqxS0/2BR8+7F5MU7wX86f6XC98E8R81PT1dPXTnefdjUmKPzwfsBXyXn3dHJiX+iYZeuk/9LdkN79n9j2Q3+eKhSGPPr64qS2qzWUVq4Mektvgi4kfVj9hLV3ffTmazK1S/+nkyG3wx8W9t6KGFL4n6MggidVXymnthUVZN2Euivvyz6vcH3ktWay8yPicTFxa+/uS0+A9oUV2RnLZedLxLhh6wt/uTJLT3o+qDplJgxdOAJa628AWeXcHY44Pm1JvP3q3Jgau+AGXPp/76rK2t0KyWFNDyCNAixaZu99VnakuT3r7q7OT0bDLgZzZxYdBUX3uGlvBzUH9OVs8mA8A5xeBTb3i+/pOT+OdVzVj2+fckt3svJrLIz+zdAnsgdb35WY4/OkS0Oix71P8ktZMvKrLeJd/6KpKRDAGfh9jQxSt+Kh+w1uNXU8TH1V1EfvlRZSJX+/4rXCpq57p9AbrEEX1bpW1OdfyqfkV++xx0WwGq+hud09Y487QoEGDWxEIyelmTUx2XVZUaof+Q2fOrRQ5i9/a71egStXoe/lvzS4O4SF/4V/b4BcIxH59kl2X20gPqfSJEzXBnlU8736cSxx3VFlNEXABO+v1cKftKx1666ntkbu3O29sdwFwxYTGP2impIi5Ay0gH9pj36JKePb/qf9dI3+3fDgUg8IapepccJJM2PXDrb+r680fWLZ9oxRvGHtDne1eavGf2dvsD7Cw2R5lnK5WsiyK05HPxeA6kp4G+QP+5M9qnWScv9VerdNAhprrphbfIwPP7ns02nlS4D2SJ5tR7h0RtmRAS8FWv6O/vX3HLF/Bx5lDkg8aNmHUcSBEvqIYraKSp/+YH5q3iPhaBP6AtIDOHtGGipEDGFZ3IKaPkIfyKyJMjDo/M2DOBupsNWOZY8PtTKXnjkrbGybGuB1wg2HJHxx2XFqkRNGO4ppHnp5ouPejMntrNzTfuyE+pWQsmBjbm5RFzkXvmzeFXr/Cz/8G48/uxWE4RgImByZDjrLdNhK4AKbslu5oxnVqzNu02Js9gkZ4R3aOGKesTAzw4Wwh/cOnv7PtzB9hneCzpXefZ3VZC16d2iyZbVjVbIFNL1oJaR7+6+k/9R+YqC5i7cl6GOPBSJlyLkXWLMBQw+n8fGCxdbdjJq+NCPvDSnz3qO7mQjYxbPKKMjvdrektXVXfrPaTCwPP7bPx/UxJFlB/mXBJwhwtSZIeoNy8botnCwPOljjeKgI48869+hooNv0/1958znvCVGC8XTOSUQFkRlQp+n2lK3Q3V5/dBLLv7qGnuKDcugLxnyTWYjGDS1tKNuXf3oe7fzlnoINyqTT1FBeZlNfv26n3vl2s5UQQm8nqK4xNiYWi5Tc6RWh2uih6+CeS4THLc4eT5/Z41DZZVqpGXOkl5BMfEiITnBR/CRym85EG0URg6JpqeLa5J2UEpZpsBVghasM9rOryY1ued+kkPugNoQpGv43y9RFenmpYn6bieyROnPCx5ydiHMJkgzbt0/25vV4tTPt2XalqepGkADnm6+hMpjBtI0v6hyYJ/6rydPm/yUnBGIfJSq0rLV3pPscc1TzTNgPmUIu+awcse8BT7kmVteiCVYj+6LFoE1dOm0WOylzmQQoUKLmvbTSR43CP7QCYvhXIF9prEdjzukRX3XHketpMZR02iij5d0oATJBU5hRxSN0y4C3idd7o1L0WU5DKzXICAzyS6Y4t5sONCCoanwubuT26aJM5OZJutzj5JhbICF6UtenR7/ERC/fPkTCq2I2PqwiSFwq8emljx1fcCsoFWndyuvmgwy9b2qY8mullM3io5xd2hd4wpizDsvEoKjuxjUv6tLjl3auGo0aoIBB6xtOyJQDaQ1UNTtTDDJ/cNUxY2xD9rBalz0tibqjseLxukLGwrMyQ0esc5vxh+nJIW7vF+w+4A2FKWlKjDMVUqjTH1lr29PiG2TTM8k1XzTUriU31TrCzI1X79audTDyXR/XZVFOKqxyjSC45L+tXOFzh0KallLrPEpzOV9mKc7NbZFDDqjj6TemKGX4Uldcroytm/ycMOtn7u/udfUX3i2CE2+PzGXQmTEseKpNUOlJPuv+otGGf62Qj3TQUXwfFHohahpWT/lW8huFxNn1TAo1P6BcRX7Mvgndq7n/7F2STHH9F9G2r15FZYTt5n0wgxV3Tj73jnz8VuUjNkUntGs3+lgsKnqn5gzjrdOJzUG5/bDVsPJveejGO70YyFERfwV99/YJJqXPbJxb1Hb/R33yw6dKjo5or7V47uvZikrNhrWrGfSWvlnrmiqgFUi6Jo1dGLBpUu++Tlo/eL/IhZOAeGCWxR0X5NL7qyNylFzu/cqPbBgJ+MQmPeA7+aXnT/xoNzJvLh5IP+IvheQKzBo6zR6e9+mgzb48xeKF4zGcvTnHl67rbpTv8z5x4BcfriKPr6Keqh5IQQz5zrN+7ym6SYt3c3jDhb4ggC9gHYrItHr/R396+6cuPXB3vPXbx9xloUZU8V8hYee/oIVjq8ytlDDdjMt1+hJFIg8Aq0g1dMf/Wtm/ev/Lr34u2k28svGLJvX/7t/iGk9tkSaK2k7QFF5BUJflgqoWqoz/9K9c3+o9dOet6BNbkw787TKzAE7aawpW16U5Wpk1hEQtt/6/5vZoJqSuH23hsgPKz4s6o3+641d5zCgO+Vm48uT3UCTz7oBjeLeQULU5kBVUGdyMMMwhB8ZcXRi1NFXljgk0tiGUaHEOLC6oAr7iiB/qJHNlbhlMDJ324Z01d8tHyviP84Tlo9gQHfrb/FH/EcsRBKzxrikkbHH7xX0yN5mL/uB1O8OBf4MXXkGZ0iK7wOPAJfoPrG1K63clxXd8tYL+DYBLlDww9c2FO6ePIeXaaiYQ9j0cTJ02Zv/1Re/N7TFdbXRcA+t+AOWxjIAwW+GtB8QMgicwONNvgVzDeyUMLRVUl9qd+LBXlfhf4laKuM5MGb4cDOe+XWzRWr+vv/DbjSvar//qruFSt2A1bAz6Kiak1t1szggBpYNXXXvkPS9ln5HUhQA0Svx4Gv9cqDc3eO26ly2fOOn7x4bu/Ro4/67wOX1clJLXoRwUt/aoue5Aj+WR54Pl91/0S8zllT1/VySxx68i7GItG48Ae6905x3c07xIpk6WI52rSToiPKn2KVQV1CqIUn71wW3SkpsN9iQhD39PjThZkpzNpkp/GEC7Y8fOP0cOHs5MaPRbR2aBj+qfAvuwVArKvlD3C31FWqrQH0CWTZjZ1bOpZuL1xZ5f1+DVsStV0KQWZJ6aLOv4TBV+ktlLc99C2vcVlbZ+v24Z6epk/3tX8/HWHxjvZF9Wc7zb+rWCpE2ED7FZ+1cupi545oKEg6tjw3mtjihcGCRIh9K4pQ6fhB+CivJ7reQ0sOaGfN17k4++ySytEFJbmxzCD9ZkYszx1NjM/WXSgWhxIkxhVGnirUxmz8JdfQamZ0PA8+yu5cW+zQx/Vrad8yS6KlpdES9hCiOaOZitLmjhg3+J11L+KcmvhfM7L2l2wcfe21wUEgdTk/mpvYIl4pFIwWJcZNuuQJG5rD01kz8ea6uuZcxkW0MgqsLrLvYwXwo52dKERsAw4OLyHHNMzxwI4DWnir6xxProhGS3LFjgCCK/nnVZ09iV2cv+nCDKHvR5dqEe5Jp0seT0ApjJPLSysK8JHG4d79wg3X2nbxHXLWdMIcRt4iPpGnO35Nt8gSuvXY3SV5bedrRfY26T7v7GVL9fJe9hU+51sO/H5qQtyhWh5f8KZT6qSJXzbOb7nArnMf4nNqDHM7TBtWRt19TRd4X6RhvuvLvhSummn4NG8Rm3hdPfQgK5ss7J+9RGZtwE+XjM3kugpDoz30kYRswj8X8Ck715h8VhwjE8L1t3QCF7aAxe6v+55f9bXJx41R9nFpAz4kqHpMobuByeNs0kXkC5M282hfGy179a1Nl6CB77QPI9KEfgasF7lT9nu4kq985aafJ9jn8dXagfe4qseqQ63C5LFJ+4P9U+zFn1qK2+vk8ncsPs/Gcz9Z4vZTiTzlJ/dX1rGLOs1PoKMA2MMej5ts3gaornJTW/N8dGPUPKeHiNu0FJcbyfVmk1bDQk1sJMsc0ERjJtPZrB6ZCRYxboxrHsYYO6NW+5vXJqO6CryVT5K0ZGQpRyzvqsnSHRYfzieX77LutTY2jevphIBv9xN9YkrEvVesx5G8hVzr+xb9vYelPfqK8Jp//BWkqbAUjCxyQdDGBkDas5Wu8gG5m522f8SGfI9YjO4VEmTnBteXbnMkTxTJ2kS6z95hVo1dA/CaICQt6F5Q2mTc5rZo6EQtPltArn9i129g315RdA1t1V+ctpp9SVsdSsIMds3rludwxXQE/ckcyjSCdgzNWh7IzZFmuQVAHpeYfxKmt1tid/1PpDPPjLe1e4F2xxUWy7VWj6UuyBOsFyRxs2ilHr8PB1uvAXnCK4Lo6mFBDgYIlS6i/OiwjC7dr9p2fLP9w3ENTSPdCr9gFtnq5AavuyCvnJP3C/qbvqnWTyok7QXyBCcetcu6bJOgQMM0V/T+Re/VZd/zXYpFZnkOU+hdYGEE3epL9CszqEJuL3ZDnjBvN6I/2bwl9QSBPDFhj7lSzDVHilILXYM/KnvnWvbZWabHF3iSJBu0O2mijStl9h3ncEUeXw4ykTOSuVZIDAhqi4qVAxh5H9jfutNcGh9kGtcFl99BwhxF+d3D6doag+U6VZEUZbPLi12RR0UAQFPrb9CdV0+1j5/6JA9oiefhL4OPc3PzzPHqJvdnY8IO4D+Y0yLiMmvQFXmCATOO/qaV8QLYl/xUlV4oN8pOttaS7cDUVU92JgFyVbpe8IlOmUkWz3Xsxi5VPTfSNu0hJ09bjMvIvPXhFzpekkM+zGnkQeiLoEoywIOpRIBWfQ+ePs00o3fh5oBLQe5q5J3lXwd7WolLlJQ+fleuTlbIz0YqgGfwtUdR/s/jtZpC7548LJyYfKCONLdePTdKctoB3cijr0Uib1Q6KsdpywQftZuAigGPBfYcnPU6YMvQvUtO02C5YxA0bwJ3TbgiTxh5WL3IxvOWRBn1+pxmLRIMuv4iHF8L1ysJL1di573rNQ8/ZkEpYLLKnaxzRR73HigkHoHnrUWND24mAhZMwGcpuXY9xBi/wFfsc3s+9r8LU5Q/dlcBXE7eDOuTdrCT6BM5ppEXsCiQwtVNQMy7322PFBDNdBsnu04uc21haM5McV3my62r9YaTZ+lVEfU82ibWk4m0NYKH3nTzwiXIEKLY7Gr0zqeT7p3354gYtzIY5mlkS8FGpuoFsd/cHq7Io04iQQHS7FvLMqxrhMgvIG7hpbYG8tcJ6HIx+Ipr5Gs43re4Aut1ku/Tm6rnhrwwo4KqkyR1wPotDV/rMhGme80xESJTGkqtw0UY562os178t6JP5fmJByOCG1XPDXk8rsnlmPYKSJu3NHAHD0au15WPxwcwIp/anq4bqiK+sbgEL3C6YVnKLnOh6rkhjwWJgkImB0r5sXtLwxbN1yNgrUexW6EnodYmu4XG68xgteRpojVTZ8Zyz7oLVc8FeWvYKeJTgrL5/oBdFmO5Lp9D6fIYsSnUN6C0WBns2aPxeKiGTrlIjQhLn6yWZKF3oGSzm7pQ9VyQR9NGlD/Eo/ACTepJtkAjc69QjBIt0SXWN+sbiA+bn4nU9IY8mr+0eJYIq9UWm2YGfY6reiccO+hMHtP3NUcoRxFsQHHId1+r//JBb9aW6GMg2GyjQtCeau5uR2hjwji8vKh6jhZGGdWeFuissCsqjZ5Zo0e/8Cm1br20GCcMGX6ZxPlmAqodunIMZGnz08Rpxs0bR1XPkTySc6OU6j+4pLp4w0UBVxEpvA2+sOCIJcixio14Ig/73x+PLeDYeAEwxhV8LbJhBwfy8siyU2Nc7D/3uXqTly4TBDDqpLLJMA6+XIssFU/kSfazOWxSFjA4eVIGKMEBks6VY5JKvEfeiWEJ4+Cr8abzZRtWvqC5weGFPDk1ygJOqh4nz1j8uRA/nZq15k+6SHX5kozzBp3DY6ZEG/fs2zXghbxf3JDX4tAIJ0+mOTu/CWsa1gLyhuq2lPJ6rrcTGFZQB9AMZdvvRV3YbsjTTDMnOESOBfIGerZvKc4/dbh4y/D5xAhbaIKlVuvzZQ8v9TlAI+EUXpNiG/X8zzWeQ+MxLsjDkfXK+tNvmIDrp1YuBQJOniViFtrFe15eWJull5o6rdEZB3SbMoxjzwN5WBW2SDngnmwHVY+Tt1zTyWBjRjAYlNWziMUC/7OnUo56qek5vLFaN/h+0J/gnrxsLbXC8vmxx+Tg1ePk3auaff3q0LL1GRkZBxs7eTIygoVi6q0MYRlP0dVg5e2whs5XcF33sXvysM/H0mXHTTR7VY+TVy9/wF3vCF5yZ6yhM/XN0r3tUS4tnfp8ePfkaX4i67wAbqLZx045efpZUCh5gz0apRZYL+38CHrf1h2WlJb/yh+6Jm+h5n+xiahzWfwvu3YsRx5ot9Jj9h6IMIXkK/CeECA3oEvHcE0eNs1srGzujbdV9Th5xpkZlmwDTwFUa0ge4onsXBRXTtmh5Jo8bfzb+evw0ESwTTLk5JmZPJJ885A/YwchCDwBmQH4hl8vuzLdkodNM1vHFd9hYRfA5eS9ZfaxpJ296dAplxBc5nZbqKzB06i6JHnvljycSWSbhMRDMHYaFSfvoennknqR49Arl/iDt+i06dYUa3hoTlq33JKnKZz2Gc/ZXCO3UfU4eR3mJ0jR/wlNMyNY9q9iHxKzAt0lo9vI4pI87H93iMtyVc8mydBh2gKksefkZ3AHnhAwsb0UPBlG0qBckqf533kE2hw8M9pG1XMmL22ayF5yZi6bFCb+gUL91nwTME/mNPGoO/JwapTjKOCqnrVXzwV5cvTeceaWu8itYJOi2fhZn4uIKXNPm5I3YHstDuE7hlK4B9y6O27I87bu9SiVjjL0hA15kDfhaHkM0+slpyglz3bfFdZCnHc6r+aqnuU5jgJDg7TuObDX5iKRe73NLh8gxjF2yFYkU4FhO/IwKS7sJReqnpOqQvDEPXtVEefISTaJjZgtoZ0ugvWMPFNVRZrLeuCkFheZ5jxDx1LV2+Jq5Omkhj17IA0ck2SoxDDJwGiEoeGU30V7LctMSp6tIakJAtttcQQ88WK5VbEVV2segjj2gt/bnQmWo5PFn0e9rSZKMtJPnYYedeyZm2d2G3jwmHWVU8D3K1oVW+FZQU75g2Katq1+hvQIh2A7nXamJKEQgu3T4Tn/8mpE887tpAFmxNVOAbaD0DJXj5PnmMMkbC6xDX8he3jMvika+DPVtjQlzvYNN3irooGlYto5aUVbJzKMlTyXVUV43MDCq8c39xj8eQZIwf8FlrmeWo6mvZeYLnmm67bmjLCVOXQS6IJbeVSGi8/kuhIRpgH25Lnc5cJHi8Uizwlx4SuWYgi5VvliWvg0aCfP8FewUvNxgqzNsklLhxgCOMxPzW++EOzoVn4GHkwuC71xE83C5819Tm4Mr21iWC1iERYqwNxa1wNbSOSYhRQjsWtLkb6QlH5abnjjIVuWeUUocF8JITBsVLt1hOXxQIR5Z4R6W27ak13zCdNeEFEas0yjpYlXFjtCMfmWy2oejUkbL+eBm0F887xB+J07cXHE0f1mSiFepY/UIXCJ4nJ/c1jKLjJP0yYLbdwimYlGNa0kVJj2ucTM21dM10uzucc7F2tqm7WsAp3LvSJl1Ivqcjvgv4SU/v0m+oO4R85l9TM5TX2zycrHIlxmy2gBzZV9w/IOfDa06LPRGukyEzJ1o/L0aQAp0kPXv3AFnzUDbpLLi6V8lpg+i6xNTvqNustXL5ZC/5EcA318HV2gH5nhX8iqGbExIrhVCZkytPQgoKFwLV2FRiy6aiyrCGK/rGr2cNMo98AiYkfbewpntuYbH31Gcfmpw4cLx6cbMuNKEj1b8tEAbFh5tilHCqIi1JQuKmwtb9vkENQKT5e2qARLh+WvIgrlWlp6EF3X2UvnXIldFS053p45mjh/9qfCh00jfE+itU4qqfIApIBlybu5RBj10bmW52rYl3a90pAxJ+GuPXlo9sj7ozJfbdrCfZjCbmVAcFfpjvo54+cTpaxA4nJ7tahCiSe2tB1I1JoXNM391G47UZN0Ks5o/y8k4EBHTNoypkEJw178EvSXabJ/zgROeWmIvkWGYR2nfp42pTZxvqM+EaW+ExmZCYe82vWFRIo3jidYmVV68ci4g6KxcoResotFSKoaZxeUn+r8urh1pobizvKvO09tOiyU+qQomIFPQegsLkZnfv11/ik4+XBbW/l1UI/CK2fOPDGj44vxjrc2fDGnAmPDFxveeqvj4fC2LwSt0gZt50tZEVUMYpGupr7kcGFCvxcjOFrhbSdQ43DTktp4ZjASycwt3THsplTwsp5EX19Ok7tv8RzRWNjTlFhb+dprI2sHmurNtn0sG2+KlnRFYOJkQp3k8WUTu09V45rGv65C94uNcGPGUGOyylS+xEu8xEu8xEtQVNU31YOmIcrXgg7RlBrKCIdnbUJ6S/bQUAOvYjhr01C4YRPS1xvaZkF2dcasBu1HhulLFqQ2Z23KEO6XAX9lbIIXIJTlHz6YcXh46dKOs/nCpcvyhzJmb1/asR29I0FsZKghjO9I9qrO3jQrHB4aKsuHDzI2bYJeZ6RVwbGhIaSvtrIMgYdN9RCCS4JG0VRT2d4ejQ+KTdVJPrPTzbFYrA/dOfz7YCzGXMMZ+wZjoSXIJgsrQTglTv7HTHeHbRa9UxkDJbEYszhODcRjuwbgoqz2vkiwpOmz3xOVC+IjjL8ZT0LByL7PmpbEm8WWM/ZVZsZiuXFATY2maNb31cRi0dPhRYORWN9H90LL+2aklU9rrvmwCciDwAG2U8/Gou3tpfFm8flMDN/i0OM7imgAgENBtIcLIsx7WwWOCp45UPUnjivmd43nr1y58mMlDj/yO++aFdUDI1V0zuSDys8dXYXMKXRBqdR+NvRkKktYsBMK9Wkd2SqHOsu2Kq/BDfPzt+1sx0cgRxcFnMIXoJfhIE7eiOLK7ZDouR39/Ak7zitcxEIckEeDamPk7lq7XaWyrzvOveuD4DHgwcTHeG9QEx6Nb5CtQhvw95eA2hTDgOEQNMQLdO9cSn5pJ+QB6pQS6v4+qCgZ6GdWRA4zt9Mk0O8/JkcWYBN6vlZQGB/KxBy2KkHNVM0l+2m+feYisvnUtl4tjLyu6XnKcjHEHcPPTPu1HmKAbMfEXczWQ7yj/iPlNe1ngckzDfWGpf0Ey2pmgzeNRsqydtJI9jROHsTMaYbIbEIeOHe/E1sdUAhpBdvIkW0kdlmrnNjaq/12QsErUp6Sqf2MkFmV/cwl28NBY8hgPRSxCim0NwgCeaFpKJGLRqYJecR9QMkzQR74zkPi/pxlyhDEPCKEPXPyIChEZjYjL6HExGYZeQyQe6AJpgNgouJxW0uDg0G8xjRPrMSnGaAIXqVO7OREkKtODJeJ5EFvIZhNJg8hj8CGvN4galMoKb0ssjQtu0TJxCFxc/KAbvIHI69ULktNyVt5mB1ajFccCKHgtaSMDYNcXGkbHkmzt+IV1gAm4rIPOgjurnBE3HogkocWGdifgUWla/KWQ5tQcI8HJ5ZFYLd7Vlyp0RZzC/KiNNGFkdclewUHSKJR3T12aD5ZcT4luX6L4LFhrCXCBpLcg+etOuoR9SD3SgVHQrlSmH+4IFcMiujJQykY2pdwS16BMgxt7hLa1MhLm5erxBB7FuSxSQrkafrlYl2+2oASGhu7MLaV9w+tdlrX5ihBbYnNZNk0YTrDtoCsWuCteIUlCiDEFuKrZ46yHJy5QVHVM5CHNo2g5cgteb2kTZ4vg8lLWx1S9kOQ24K8AVrzfrYS6Xh9xqJojc61O6B8+BHgyc6z/NgcLDIg7oHkWgGtQigijLY2JWeLH+gRMPhYsDQyHWlOK5cL4VEjeSimCbFct+RFErNRm5lc1SPkpa2pUeIL08JW05bEk4G83z+D1yhlimIMQKftN4KiBXVIgK+3Myu0R1VnngR2AhzvDrujXaOgi2UnzSHaUZ2QhGFCHggt4HurO/IOENVqM2+Tkpd2PYKG15+m5HVR+QzTFs05SGiRCx5QgbFsSDjYooCOUrIRxA04jK02UMB2taAhC2KC+DqikKBSLmGxWFD1zMhDonL1HxJbluSVkHW/mGdIMvJQuHu0bKsZedtYsgYVGJDtI1W1NqoqgDZQ6MqAuC9BY5ijWO1VhXeI2aeYOmM7nQdx5ZT2M8zKOoV4FqFA3n62rwuCjLl3pV1eVuSFmbbA2+TkoUyK2q3UwhDJC7EsDyZtIVFXNNA4edcFjWGXsn4DyNgw2HSvGl64sZKGUhPKZ6a9dY+zNEEipmCVcjEoeRgfcJUqzotfgZJMMQ+yAj4SG/vMrJIDaklok64OVRFeTwtlSFEq93HyNvIs0WWUPKSXCklr+1hOdEsfP1qhbOxCcv0d5dVMQ7JDVS5Ja6h0XdPfCg2kXNoPNBoXYQYo7FekSZ2ZPNclIuTR7onJ5C22yCL5k6UR5bEsnQLRhIGte5S8zVRGbIsHuQsFPCJUaEKUnytWI7S8ceefgrxFpavQT8hFMkk9jN3Vlo5/TayutIS4Em3q6CnFC3FWfbMS2teB1uazn/XBi+Sa0PN+CDk7O9uRLtNQH1UiidPMIlmzk8/TttPt4IwpPa13R6E2Y/s6kJq2nbV58PdcZefvvGbv+zhLu+xhYieccPp0U6K0+QnzHLY23YUcItpyGyghpR3wXGeeXgt33L91166t4OsRQ4V1xK9RYpbgBPpP09mzOZ7LzZhgdVX9kyUjfVhaZG2YU7xt3fuInLfh1+ID65BetQ1+27YOWaFlG9YVn1i3gZtz5Zyq+RvWnSguXrdBP0+y4Jpt6w6gp83bXL/uAPwiRE8LNb9E2dK3Xj/1+luAh9zeSkvb9NbSU6eWvoUXZUD+vb4BuE2xdsc5FevWVcw5USw6MspzsHlUnmMSRVxdNWNgSWWfmc/xJV7iJVICEEBJepsHV+bL4RpPCOevdAjPhDMyzF+o5YyMlflE77HEwXw3qSr1fc2D0Xv7EpV9gl8Cluh7c9+cNvc1DdO0ToY/mzttGj4wF2nmQ/vg77n7iFnS8ebcaXOnsbf2Ni5pjlb2VUYrW/O1xzJ07+OPp32Mr35T67h2pI8c0T+68EBz5ZKRJfWazZXx2Zvs2o+12y1rHxwcrNx3b6DvifgVC6AH8E/b1nca+vPaNHQn1O2507jbY2Xl6Ehl30h0IB9H3Jai7yF8L+2cwWjlkmii3unpDLVuVWLhcF5hnTIoOPAyDv8SVEpylgC2YiUgvBKqFYyuhQOVO1EYLKMT/h5rJUHG2cN3lbvb6PNcpITq4YOqYUh01I5lHF73pxLLQVdvDGpPSTsSwkfE7QcIC3N3gixtI+rTrE0HdiqRtejMuogWWZq1CRwZ08INB3tCiuAQyGsFhaZuu8bvpsKt0Dn05fOhPsdj/mr4JcrIdiCtqgc8iVr0bKgTUt4r0TdduxO76SFCNNaYlj1cozhniY2TqMD3yn5pt0EJ1Vsv0AeCjXN4xDiyAPFGYWqVc9dPDjf/xxQ6qqI0L3qMvgSCH+GeTA0tJMgwRjcIN1Ej7BtqjNUS02q/vPeLuOC1ThAm0EEWnlkY5zWFW+gzO6gQd2l5XPs+WRHy937n8Fo9Ia9suSK5V5uV0/iXCtLGLEXBkc5s/CNDejvn4SB1bBwRYgRrMunRPmpIzaGWfZS+S4MdIYgThXce7U87NfuK6ZmDhDwIJ4ppyYLmG6TeFMj3ZzrjY3Gz1H7SIWY3py3SVul86nV8WzBaLEDJg6EmWaYllLw0MiAzKHkEQJ6wJ+9UkKx4YNUJG5ISVLONMiuUjm9GHjtC0CxX2BbIY2c2E/IgqVisXQu7Soij/wDzpjTUsGUBuVk4fiI+Ck5eltY82NGuq5Yx8nYpgm3NyTtIl01GXgO+lwV5OfJOK3o1Ja+KSQdKXpVersJbkORdvJS8KrYICeSJpghMZxJTpo41kTwweXW+VA2UvDKqHZQqEbfmB5u2Qfkl0XTNy6HeDyAPd346XqvMyYMdvKbuR7rCTWcLSZQQ0Gtwq0E9kQViULWdrHk72J58Sl6PEpK2UM8hU24ed1lz8oBpswRtIE/72Uin/B5Ihl/s7lV2lLxvdFv7SpSRH44cOdISog8kI6Js/GNsbGwBYdWcPOiKpPRQRJXBH3748sgHO5lojSrRH47AkS5jzggqsyC4jNuV747Atb+EGPGUvD91+7pg4dYivb3MCSaQ14RfAKkH9HgRfNMvN7J3AK+GjWAx6+LkAoC8WQ1VB5tydQ6IEiX+IYCKWEReZO6bgFKSGmFOXqt5EWigKoaaq+HeD3bERJkuBDdJCZOc7Urmd3BmTGEreLNyb9asqpWDI/qofw5OMojgZAEETt5HSsxMcwPyUOsfii/vQjuv3GyurFdC7fsSEcO7l0sUjaPwYzowgCzM4/+xaStIOkpePht5s95446M33phG9JGoghWSC4Zpe8FMqIWh2DVNJ2DTdkyYttF97RDBM7w4AVx4IDLKFWErEyPvnhI009zotJ0j7jEvgG1pLt6EBiMvIyMMRTJrZfcNFRjDVNmANQ8rTBn4CJAnKPiHiTSpCtKY3sK3h0H/vEDc41RgFDIHMhUY/IiEzholRBYeKjA62eoIIy+jKg/KXBnKjtSi2PACIWzKyRs3f4s/FRhhueQIbNBxLthD1rz5MSUuscdVFQK9qgJpLkJfCunDHhQ8tI1UxoiqCgVXVcxxnfmvuapCQdY8iAfpq2scQCJDTIrh5EFVLLMd21xVkQEpOY57CqjAWBNScsWTOXlr8OKjJw/OEB5NKc1qeF/Yqg0qEx23nLw9ZC3j5JEbEFTRdSxB88cEPY+sslRg6OJBAJTTUUyipxoEPa9FfvV/IZ44AnnzEQFsg2GIxMRs0EH1PGBPHHvNrH5JDmaRWRgUG5RMpg6v4cGax3yHnkAeszDSPiDWWJQFQBZLQzBvlCi69dTk4eStI6ooJQ/Fg3TstSg5JVK9khhTBeeFxKpGX2zF9wHyiO6ZNYLmSROdOXGLd3kLGGdVY9bHlRAfAyU0rFnQRVwnQX1jdeydB4XCXIWwEH03PQT/qKeFCoy0rK1EQETpW5nD+2XlJk4MjP20zlUTU9/vEkdALUuWgFRQWSyiHejSTlLBtoWVgPWzjeqjzLZN+1ZL7jgYxPrufIeaiTBGt/1P+fP7mZiVMMivnHwQ5+HDM5G0a2nJ6W2BmA0+Ez7cSE6kqIQkl74dO/pC0qv6q0Zhnyk8w4PDpZn4NVj5M5Hsfwc1B5cg1UQ+IvukPlairQ3hzlqstM+eWQFhns0tOTktlXgG5rX+sFP537bDWJxA1s7y8+KiVSuZOIdB4348g3a7MQovL4DZWtWag9XpqpnbIby1q6U3pyWnmchXCKwvSwvPidQ61fUGx9eb4Puiq8KWyljzwJq0hkXT63J6N7+qYTN+Qp9u7u3dnNCFOjuXoM2WmVGdU6lwMDbY92RJZTsRFxU7Nuf0rsXN1e1ACk/FYvGIfHXx+b6RypHmKP7GwzvWru3NIWf2omex7CPU5zc/Io2Hm5rjUcGn8X5M3Ja3SNft1pF4c+UTiAB1aI+1YEdvXW9vHW4+BwvAbU19lSPR7wRv10skG/8P3Eh6vM8y1AYAAAAASUVORK5CYII=",
					"size": 11
				},
				link: { "url": "/", "label": "" },
				items: [
					{
						"link": {
							"url": "/contact",
							"label": "Contact",
							"active": false
						}
					},
					{
						"link": {
							"url": "/donate",
							"label": "Donate",
							"active": false
						}
					},
					{
						"link": {
							"url": "/get-involved",
							"label": "Get-Involved"
						}
					}
				]
			}
		});

	component_2 = new Component$2({
			props: {
				dow: [
					{
						"link": {
							"url": "/rlap",
							"label": "Refugee Legal Aid Program"
						}
					},
					{
						"link": {
							"url": "/ucyd",
							"label": "Unaccompanied Children and Youth Department"
						}
					},
					{
						"link": {
							"url": "/cod",
							"label": "Community Outreach Services"
						}
					},
					{
						"link": {
							"url": "/ps",
							"label": "Psychosocial Services Services"
						}
					},
					{
						"link": {
							"url": "/education",
							"label": "Education Services"
						}
					}
				],
				imeg: {
					"alt": "",
					"src": "https://i.imgur.com/XbRkfNe.png",
					"url": "https://i.imgur.com/XbRkfNe.png",
					"size": null
				},
				link: { "url": "/", "label": "" },
				items: [
					{
						"link": {
							"url": "/contact",
							"label": "Contact",
							"active": false
						}
					},
					{
						"link": {
							"url": "/donate",
							"label": "Donate",
							"active": false
						}
					},
					{
						"link": {
							"url": "/get-involved",
							"label": "Get-Involved"
						}
					}
				],
				next_slide_time: "4",
				testimonials: [
					{
						"images": {
							"alt": "",
							"src": "https://i.imgur.com/sUWuKJS.jpg",
							"url": "https://i.imgur.com/sUWuKJS.jpg",
							"size": null
						}
					},
					{
						"images": {
							"alt": "",
							"src": "https://i.imgur.com/QfwGDPt.jpg",
							"url": "https://i.imgur.com/QfwGDPt.jpg",
							"size": null
						}
					},
					{
						"images": {
							"alt": "",
							"src": "https://i.imgur.com/uRlsBxt.jpg",
							"url": "https://i.imgur.com/uRlsBxt.jpg",
							"size": null
						}
					},
					{
						"images": {
							"alt": "",
							"src": "https://i.imgur.com/DO6qDOh.jpg",
							"url": "https://i.imgur.com/DO6qDOh.jpg",
							"size": null
						}
					}
				]
			}
		});

	component_3 = new Component$3({
			props: {
				dow: [
					{
						"link": {
							"url": "/rlap",
							"label": "Refugee Legal Aid Program"
						}
					},
					{
						"link": {
							"url": "/ucyd",
							"label": "Unaccompanied Children and Youth Department"
						}
					},
					{
						"link": {
							"url": "/cod",
							"label": "Community Outreach Services"
						}
					},
					{
						"link": {
							"url": "/ps",
							"label": "Psychosocial Services Services"
						}
					},
					{
						"link": {
							"url": "/education",
							"label": "Education Services"
						}
					}
				],
				imeg: {
					"alt": "",
					"src": "https://i.imgur.com/XbRkfNe.png",
					"url": "https://i.imgur.com/XbRkfNe.png",
					"size": null
				},
				link: { "url": "/", "label": "" },
				items: [
					{
						"items": [],
						"lists": [],
						"header": [{ "heading": "Psychosocial Services" }],
						"texter": [
							{
								"pos": "Psychosocial department provides support to displaced people and vulnerable migrants, focusing on their general well-being, both personal and within their community, as well as their knowledge and skills to live successfully in Cairo. The role of psychosocial caseworkers is to work alongside their clients, and conduct assessments of their strengths and resources to help them think of ways to solve their problems and relieve stress. Recent developments have made it possible to expand the psychosocial support provided by focusing on developing the skills and knowledge of displaced youth."
							},
							{
								"pos": "Clients can approach the StARS psychosocial office and receive information, advice, referrals, or urgent assistance. They might also benefit from longer-term support from one of the many psychosocial programs, including:"
							}
						]
					},
					{
						"items": [{ "subhed": "Adults and Families Program" }],
						"lists": [],
						"header": [],
						"texter": [
							{
								"pos": "Caseworkers assist clients facing emotional or social issues and difficulties meeting their basic needs. "
							}
						]
					},
					{
						"items": [{ "subhed": "Medical Access Program" }],
						"lists": [],
						"header": [],
						"texter": [
							{
								"pos": "The program provides medical counseling and advocacy for accessing medical services, as well as medical grants for those unable to access free medical services, often when no other organization can help."
							}
						]
					},
					{
						"items": [
							{
								"subhed": "Drop-In and Emergency Response Program"
							}
						],
						"lists": [],
						"header": [],
						"texter": [
							{
								"pos": "Clients can receive preliminary screening to support them in accessing StARS services according to their needs. The program plays a crucial role in identifying the most vulnerable cases that require immediate intervention and community support."
							}
						]
					},
					{
						"items": [{ "subhed": "Community Hosting Program" }],
						"lists": [],
						"header": [],
						"texter": [
							{
								"pos": "The program receives referrals from different StARS programs of vulnerable adults and youths who need to live with the support of a host within their community. The hosts are recruited among StARS clients based on their willingness to support fellow community members. Equally important, they are selected based on their understanding of people’s vulnerabilities and needs. Through a panel, vulnerable clients and hosts are matched and supported by the program’s caseworkers."
							}
						]
					},
					{
						"items": [{ "subhed": "Mental Health Program" }],
						"lists": [],
						"header": [],
						"texter": [
							{
								"pos": "The program receives referrals from different StARS programs of both adults and youths. The program’s psychologists support clients with psychotherapy for a wide range of conditions, while the caseworkers support clients through their recovery process. The program’s psychiatrist can prescribe medication for those who need it. "
							}
						]
					}
				]
			}
		});

	component_4 = new Component$4({
			props: {
				dow: [
					{
						"link": {
							"url": "/rlap",
							"label": "Refugee Legal Aid Program"
						}
					},
					{
						"link": {
							"url": "/ucyd",
							"label": "Unaccompanied Children and Youth Department"
						}
					},
					{
						"link": {
							"url": "/cod",
							"label": "Community Outreach Services"
						}
					},
					{
						"link": {
							"url": "/ps",
							"label": "Psychosocial Services Services"
						}
					},
					{
						"link": {
							"url": "/education",
							"label": "Education Services"
						}
					}
				],
				imeg: {
					"alt": "",
					"src": "https://i.imgur.com/XbRkfNe.png",
					"url": "https://i.imgur.com/XbRkfNe.png",
					"size": null
				},
				link: { "url": "/", "label": "" },
				items: [
					{
						"link": {
							"url": "/contact",
							"label": "Contact",
							"active": false
						}
					},
					{
						"link": {
							"url": "/donate",
							"label": "Donate",
							"active": false
						}
					},
					{
						"link": {
							"url": "/get-involved",
							"label": "Get-Involved"
						}
					}
				]
			}
		});

	component_5 = new Component$5({
			props: {
				dow: [
					{
						"link": {
							"url": "/rlap",
							"label": "Refugee Legal Aid Program"
						}
					},
					{
						"link": {
							"url": "/ucyd",
							"label": "Unaccompanied Children and Youth Department"
						}
					},
					{
						"link": {
							"url": "/cod",
							"label": "Community Outreach Services"
						}
					},
					{
						"link": {
							"url": "/ps",
							"label": "Psychosocial Services Services"
						}
					},
					{
						"link": {
							"url": "/education",
							"label": "Education Services"
						}
					}
				],
				imeg: {
					"alt": "",
					"src": "https://i.imgur.com/XbRkfNe.png",
					"url": "https://i.imgur.com/XbRkfNe.png",
					"size": null
				},
				link: { "url": "/", "label": "" },
				items: [
					{
						"link": {
							"url": "/contact",
							"label": "Contact",
							"active": false
						}
					},
					{
						"link": {
							"url": "/donate",
							"label": "Donate",
							"active": false
						}
					},
					{
						"link": {
							"url": "/get-involved",
							"label": "Get-Involved"
						}
					}
				]
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
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			transition_out(component_4.$$.fragment, local);
			transition_out(component_5.$$.fragment, local);
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
		}
	};
}

class Component$6 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$5, safe_not_equal, {});
	}
}

export default Component$6;
