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
	let { testimonials } = $$props;

	$$self.$$set = $$props => {
		if ('dow' in $$props) $$invalidate(0, dow = $$props.dow);
		if ('imeg' in $$props) $$invalidate(1, imeg = $$props.imeg);
		if ('link' in $$props) $$invalidate(2, link = $$props.link);
		if ('items' in $$props) $$invalidate(3, items = $$props.items);
		if ('testimonials' in $$props) $$invalidate(4, testimonials = $$props.testimonials);
	};

	return [dow, imeg, link, items, testimonials];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance, create_fragment, safe_not_equal, {
			dow: 0,
			imeg: 1,
			link: 2,
			items: 3,
			testimonials: 4
		});
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

// (265:6) {#each dow as {link}}
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

// (271:6) {#each items as {link}}
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

// (282:8) {#each items as {link}}
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
			attr(div5, "id", "section-dfb8112b-4a4a-4e2e-894d-a4c1fe18945e");
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
				dispose = listen(input1, "change", /*input1_change_handler*/ ctx[7]);
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
	let { testimonials } = $$props;

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
		if ('testimonials' in $$props) $$invalidate(6, testimonials = $$props.testimonials);
	};

	return [
		dow,
		imeg,
		items,
		link,
		isDarkMode,
		toggleDarkMode,
		testimonials,
		input1_change_handler
	];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$1, create_fragment$1, safe_not_equal, {
			dow: 0,
			imeg: 1,
			link: 3,
			items: 2,
			testimonials: 6
		});
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
			attr(div2, "id", "section-bf6ca704-2bdb-4fd5-b1f7-7dbb36eaadce");
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
	let { testimonials } = $$props;
	let { next_slide_time } = $$props;
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
		if ('testimonials' in $$props) $$invalidate(0, testimonials = $$props.testimonials);
		if ('next_slide_time' in $$props) $$invalidate(10, next_slide_time = $$props.next_slide_time);
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
			testimonials: 0,
			next_slide_time: 10
		});
	}
}

/* generated by Svelte v3.58.0 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[5] = list[i];
	return child_ctx;
}

function get_each_context_1$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[8] = list[i];
	return child_ctx;
}

function get_each_context_2$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[11] = list[i];
	return child_ctx;
}

function get_each_context_3(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[14] = list[i];
	return child_ctx;
}

function get_each_context_4(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[17] = list[i];
	return child_ctx;
}

// (59:2) {#if heder.heading}
function create_if_block_2(ctx) {
	let h1;
	let t_value = /*heder*/ ctx[17].heading + "";
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
			if (dirty & /*items*/ 1 && t_value !== (t_value = /*heder*/ ctx[17].heading + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(h1);
		}
	};
}

// (57:2) {#each hed.header as heder}
function create_each_block_4(ctx) {
	let if_block_anchor;
	let if_block = /*heder*/ ctx[17].heading && create_if_block_2(ctx);

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
			if (/*heder*/ ctx[17].heading) {
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

// (66:2) {#if item.subhed}
function create_if_block_1$1(ctx) {
	let span;
	let t_value = /*item*/ ctx[14].subhed + "";
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
			if (dirty & /*items*/ 1 && t_value !== (t_value = /*item*/ ctx[14].subhed + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (64:2) {#each hed.items as item}
function create_each_block_3(ctx) {
	let if_block_anchor;
	let if_block = /*item*/ ctx[14].subhed && create_if_block_1$1(ctx);

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
			if (/*item*/ ctx[14].subhed) {
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

// (71:8) {#each hed.texter as text}
function create_each_block_2$1(ctx) {
	let p;
	let t_value = /*text*/ ctx[11].pos + "";
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
			if (dirty & /*items*/ 1 && t_value !== (t_value = /*text*/ ctx[11].pos + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(p);
		}
	};
}

// (76:6) {#if list.ls}
function create_if_block$1(ctx) {
	let li;
	let t_value = /*list*/ ctx[8].ls + "";
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
			if (dirty & /*items*/ 1 && t_value !== (t_value = /*list*/ ctx[8].ls + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(li);
		}
	};
}

// (75:8) {#each hed.lists as list}
function create_each_block_1$1(ctx) {
	let if_block_anchor;
	let if_block = /*list*/ ctx[8].ls && create_if_block$1(ctx);

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
			if (/*list*/ ctx[8].ls) {
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

// (55:2) {#each items as hed}
function create_each_block$1(ctx) {
	let div1;
	let t0;
	let t1;
	let div0;
	let t2;
	let ul;
	let t3;
	let each_value_4 = /*hed*/ ctx[5].header;
	let each_blocks_3 = [];

	for (let i = 0; i < each_value_4.length; i += 1) {
		each_blocks_3[i] = create_each_block_4(get_each_context_4(ctx, each_value_4, i));
	}

	let each_value_3 = /*hed*/ ctx[5].items;
	let each_blocks_2 = [];

	for (let i = 0; i < each_value_3.length; i += 1) {
		each_blocks_2[i] = create_each_block_3(get_each_context_3(ctx, each_value_3, i));
	}

	let each_value_2 = /*hed*/ ctx[5].texter;
	let each_blocks_1 = [];

	for (let i = 0; i < each_value_2.length; i += 1) {
		each_blocks_1[i] = create_each_block_2$1(get_each_context_2$1(ctx, each_value_2, i));
	}

	let each_value_1 = /*hed*/ ctx[5].lists;
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
				each_value_4 = /*hed*/ ctx[5].header;
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
				each_value_3 = /*hed*/ ctx[5].items;
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
				each_value_2 = /*hed*/ ctx[5].texter;
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
				each_value_1 = /*hed*/ ctx[5].lists;
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
			attr(div1, "id", "section-8b4c02a8-7c02-4d98-ac2f-690cf1fbb20e");
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
	let { testimonials } = $$props;

	$$self.$$set = $$props => {
		if ('dow' in $$props) $$invalidate(1, dow = $$props.dow);
		if ('imeg' in $$props) $$invalidate(2, imeg = $$props.imeg);
		if ('link' in $$props) $$invalidate(3, link = $$props.link);
		if ('items' in $$props) $$invalidate(0, items = $$props.items);
		if ('testimonials' in $$props) $$invalidate(4, testimonials = $$props.testimonials);
	};

	return [items, dow, imeg, link, testimonials];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			dow: 1,
			imeg: 2,
			link: 3,
			items: 0,
			testimonials: 4
		});
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
			attr(div1, "id", "section-20404730-b7f5-47ff-9d68-45b0ae189477");
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
	let { testimonials } = $$props;

	$$self.$$set = $$props => {
		if ('dow' in $$props) $$invalidate(0, dow = $$props.dow);
		if ('imeg' in $$props) $$invalidate(1, imeg = $$props.imeg);
		if ('link' in $$props) $$invalidate(2, link = $$props.link);
		if ('items' in $$props) $$invalidate(3, items = $$props.items);
		if ('testimonials' in $$props) $$invalidate(4, testimonials = $$props.testimonials);
	};

	return [dow, imeg, link, items, testimonials];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$4, create_fragment$4, safe_not_equal, {
			dow: 0,
			imeg: 1,
			link: 2,
			items: 3,
			testimonials: 4
		});
	}
}

/* generated by Svelte v3.58.0 */

function instance$5($$self, $$props, $$invalidate) {
	let { dow } = $$props;
	let { imeg } = $$props;
	let { link } = $$props;
	let { items } = $$props;
	let { testimonials } = $$props;

	$$self.$$set = $$props => {
		if ('dow' in $$props) $$invalidate(0, dow = $$props.dow);
		if ('imeg' in $$props) $$invalidate(1, imeg = $$props.imeg);
		if ('link' in $$props) $$invalidate(2, link = $$props.link);
		if ('items' in $$props) $$invalidate(3, items = $$props.items);
		if ('testimonials' in $$props) $$invalidate(4, testimonials = $$props.testimonials);
	};

	return [dow, imeg, link, items, testimonials];
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$5, null, safe_not_equal, {
			dow: 0,
			imeg: 1,
			link: 2,
			items: 3,
			testimonials: 4
		});
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
				],
				testimonials: []
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
					"url": "data:image/png;base64,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",
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
				],
				testimonials: []
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
				testimonials: [
					{
						"images": {
							"alt": "",
							"src": "https://i.imgur.com/ThGpKhT.jpg",
							"url": "https://i.imgur.com/ThGpKhT.jpg",
							"size": null
						}
					},
					{
						"images": {
							"alt": "",
							"src": "https://i.imgur.com/qOnN4Pc.jpg",
							"url": "https://i.imgur.com/qOnN4Pc.jpg",
							"size": null
						}
					},
					{
						"images": {
							"alt": "",
							"src": "https://i.imgur.com/6ukJvFk.jpg",
							"url": "https://i.imgur.com/6ukJvFk.jpg",
							"size": null
						}
					},
					{
						"images": {
							"alt": "",
							"src": "https://i.imgur.com/cOrf6TU.jpg",
							"url": "https://i.imgur.com/cOrf6TU.jpg",
							"size": null
						}
					}
				],
				next_slide_time: "4"
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
						"header": [
							{
								"heading": "Unaccompanied Children and Youth Department"
							}
						],
						"texter": [
							{
								"pos": "The department works with unaccompanied and separated refugee children and youth. Services and activities include: (1) information and support to access medical services, housing, practical assistance, and community links, (2) guidance and information about UNHCR and service providers in Cairo, (3) psychosocial and emotional support, (4) sports and social activities, (5) specialized education programs, and (6) employment and/or professional development opportunities for aged-out unaccompanied youth."
							}
						]
					},
					{
						"items": [{ "subhed": "UCY Psychosocial Program" }],
						"lists": [],
						"header": [],
						"texter": [
							{
								"pos": "The Unaccompanied Children and Youth (UCY) Psychosocial Program provides one-to-one casework and psychosocial support to children and youth in Egypt without their parents. The program supports those with medical, mental health or social needs, such as shelter, security, community support, education, and general well-being and integration in Cairo."
							}
						]
					},
					{
						"items": [
							{
								"subhed": "Intake & Emergency Response Program (IERP)"
							}
						],
						"lists": [],
						"header": [],
						"texter": [
							{
								"pos": "The newest program in the Unaccompanied Children and Youth Department, established in 2021, is designed to increase the support for newly arrived unaccompanied children and youth and unaccompanied children and youth are still in need of assistance. The program strengthens StARS’ screening and on-call work at the Naimo Center and helps manage unaccompanied children on site. IERP ensured that each new child undergoes a thorough screening. After the screening, children are referred to appropriate services. "
							}
						]
					},
					{
						"items": [
							{
								"subhed": "Unaccompanied Youth Bridging Program (UYBP)"
							}
						],
						"lists": [],
						"header": [],
						"texter": [
							{
								"pos": "UYBP provides a hybrid education and psychosocial program for unaccompanied children and youth (UCY) in Cairo. UYBP serves UCY who are unable to access the education system in Egypt by providing an accelerated learning program that supports students to bridge into the Sudanese curriculum, or helps to build on language skills in English and Arabic to access safe employment opportunities in Cairo. "
							}
						]
					},
					{
						"items": [{ "subhed": "Direct Assistance Program" }],
						"lists": [],
						"header": [],
						"texter": [
							{
								"pos": "The program provides food and hygiene boxes, blankets, diapers, and baby supplies (for the babies of teenage unaccompanied mothers), secondhand clothes, and other forms of direct assistance to unaccompanied children."
							}
						]
					},
					{
						"items": [
							{
								"subhed": "Groups and Activities Program"
							}
						],
						"lists": [],
						"header": [],
						"texter": [
							{
								"pos": "The Groups and Activities Psychosocial Program runs a range of groups and workshops with refugee individuals and communities, including unaccompanied children, adults and families. Group activities provide StARS clients additional or specific support; activities include peer-support groups, information and awareness sessions, sports and other activities to promote socialization and the psychosocial wellbeing of refugee populations in Cairo."
							}
						]
					},
					{
						"items": [
							{
								"subhed": "Young\tMothers Psychosocial Program"
							}
						],
						"lists": [],
						"header": [],
						"texter": [
							{
								"pos": "The Unaccompanied Children and Youth Department saw a big increase of unaccompanied young parents approaching StARS for services. In order to provide specialized case management services to young mothers and their children, StARS has established the Unaccompanied Children and Youth Young Mothers Psychosocial Program. The program provides long-term individual casework and group support to unaccompanied pregnant girls and young mothers up until the age of 21 years old. The program also manages the nursery at the Naimo Center where the mothers’ babies and young children aged 0-3 years old are taken care of while their mothers are in class or attend appointments with their psychosocial worker or legal advisor."
							}
						]
					},
					{
						"items": [{ "subhed": "Youth Development Project" }],
						"lists": [],
						"header": [],
						"texter": [
							{
								"pos": "The Youth Development Project works to develop structures, support, and professional development opportunities for unaccompanied youth who are employed at StARS. The project aims to enhance their self-reliance in Cairo by being active members of StARS and by developing their skills in the workplace."
							}
						]
					}
				],
				testimonials: []
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
				],
				testimonials: []
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
				],
				testimonials: []
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
