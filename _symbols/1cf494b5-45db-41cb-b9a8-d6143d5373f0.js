// Calendar - Updated January 3, 2025
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
const outroing = new Set();
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}

function destroy_block(block, lookup) {
    block.d(1);
    lookup.delete(block.key);
}
function update_keyed_each(old_blocks, dirty, get_key, dynamic, ctx, list, lookup, node, destroy, create_each_block, next, get_context) {
    let o = old_blocks.length;
    let n = list.length;
    let i = o;
    const old_indexes = {};
    while (i--)
        old_indexes[old_blocks[i].key] = i;
    const new_blocks = [];
    const new_lookup = new Map();
    const deltas = new Map();
    const updates = [];
    i = n;
    while (i--) {
        const child_ctx = get_context(ctx, list, i);
        const key = get_key(child_ctx);
        let block = lookup.get(key);
        if (!block) {
            block = create_each_block(key, child_ctx);
            block.c();
        }
        else if (dynamic) {
            // defer updates until all the DOM shuffling is done
            updates.push(() => block.p(child_ctx, dirty));
        }
        new_lookup.set(key, new_blocks[i] = block);
        if (key in old_indexes)
            deltas.set(key, Math.abs(i - old_indexes[key]));
    }
    const will_move = new Set();
    const did_move = new Set();
    function insert(block) {
        transition_in(block, 1);
        block.m(node, next);
        lookup.set(block.key, block);
        next = block.first;
        n--;
    }
    while (o && n) {
        const new_block = new_blocks[n - 1];
        const old_block = old_blocks[o - 1];
        const new_key = new_block.key;
        const old_key = old_block.key;
        if (new_block === old_block) {
            // do nothing
            next = new_block.first;
            o--;
            n--;
        }
        else if (!new_lookup.has(old_key)) {
            // remove old block
            destroy(old_block, lookup);
            o--;
        }
        else if (!lookup.has(new_key) || will_move.has(new_key)) {
            insert(new_block);
        }
        else if (did_move.has(old_key)) {
            o--;
        }
        else if (deltas.get(new_key) > deltas.get(old_key)) {
            did_move.add(new_key);
            insert(new_block);
        }
        else {
            will_move.add(old_key);
            o--;
        }
    }
    while (o--) {
        const old_block = old_blocks[o];
        if (!new_lookup.has(old_block.key))
            destroy(old_block, lookup);
    }
    while (n)
        insert(new_blocks[n - 1]);
    run_all(updates);
    return new_blocks;
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

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[2] = list[i];
	return child_ctx;
}

// (464:2) {:else}
function create_else_block(ctx) {
	let each_blocks = [];
	let each_1_lookup = new Map();
	let each_1_anchor;
	let each_value = /*events*/ ctx[0];
	const get_key = ctx => /*event*/ ctx[2].id;

	for (let i = 0; i < each_value.length; i += 1) {
		let child_ctx = get_each_context(ctx, each_value, i);
		let key = get_key(child_ctx);
		each_1_lookup.set(key, each_blocks[i] = create_each_block(key, child_ctx));
	}

	return {
		c() {
			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			each_1_anchor = empty();
		},
		l(nodes) {
			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nodes);
			}

			each_1_anchor = empty();
		},
		m(target, anchor) {
			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(target, anchor);
				}
			}

			insert_hydration(target, each_1_anchor, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*events, Date*/ 1) {
				each_value = /*events*/ ctx[0];
				each_blocks = update_keyed_each(each_blocks, dirty, get_key, 1, ctx, each_value, each_1_lookup, each_1_anchor.parentNode, destroy_block, create_each_block, each_1_anchor, get_each_context);
			}
		},
		d(detaching) {
			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].d(detaching);
			}

			if (detaching) detach(each_1_anchor);
		}
	};
}

// (462:2) {#if events.length === 0}
function create_if_block(ctx) {
	let p;
	let t;

	return {
		c() {
			p = element("p");
			t = text("Loading events...");
		},
		l(nodes) {
			p = claim_element(nodes, "P", {});
			var p_nodes = children(p);
			t = claim_text(p_nodes, "Loading events...");
			p_nodes.forEach(detach);
		},
		m(target, anchor) {
			insert_hydration(target, p, anchor);
			append_hydration(p, t);
		},
		p: noop,
		d(detaching) {
			if (detaching) detach(p);
		}
	};
}

// (472:8) {#if event.location}
function create_if_block_2(ctx) {
	let div;
	let t_value = /*event*/ ctx[2].location + "";
	let t;

	return {
		c() {
			div = element("div");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);
			t = claim_text(div_nodes, t_value);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div, "class", "event-location svelte-mr53e8");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, t);
		},
		p(ctx, dirty) {
			if (dirty & /*events*/ 1 && t_value !== (t_value = /*event*/ ctx[2].location + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

// (475:8) {#if event.description}
function create_if_block_1(ctx) {
	let div;
	let t_value = /*event*/ ctx[2].description + "";
	let t;

	return {
		c() {
			div = element("div");
			t = text(t_value);
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", {});
			var div_nodes = children(div);
			t = claim_text(div_nodes, t_value);
			div_nodes.forEach(detach);
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, t);
		},
		p(ctx, dirty) {
			if (dirty & /*events*/ 1 && t_value !== (t_value = /*event*/ ctx[2].description + "")) set_data(t, t_value);
		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

// (465:4) {#each events as event (event.id)}
function create_each_block(key_1, ctx) {
	let div3;
	let div0;
	let t0_value = /*event*/ ctx[2].calendar_name + "";
	let t0;
	let t1;
	let div1;
	let t2_value = /*event*/ ctx[2].title + "";
	let t2;
	let t3;
	let div2;
	let t4_value = new Date(/*event*/ ctx[2].start * 1000).toLocaleString() + "";
	let t4;
	let t5;
	let t6_value = new Date(/*event*/ ctx[2].end * 1000).toLocaleString() + "";
	let t6;
	let t7;
	let t8;
	let t9;
	let if_block0 = /*event*/ ctx[2].location && create_if_block_2(ctx);
	let if_block1 = /*event*/ ctx[2].description && create_if_block_1(ctx);

	return {
		key: key_1,
		first: null,
		c() {
			div3 = element("div");
			div0 = element("div");
			t0 = text(t0_value);
			t1 = space();
			div1 = element("div");
			t2 = text(t2_value);
			t3 = space();
			div2 = element("div");
			t4 = text(t4_value);
			t5 = text(" - ");
			t6 = text(t6_value);
			t7 = space();
			if (if_block0) if_block0.c();
			t8 = space();
			if (if_block1) if_block1.c();
			t9 = space();
			this.h();
		},
		l(nodes) {
			div3 = claim_element(nodes, "DIV", { class: true, style: true });
			var div3_nodes = children(div3);
			div0 = claim_element(div3_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			t0 = claim_text(div0_nodes, t0_value);
			div0_nodes.forEach(detach);
			t1 = claim_space(div3_nodes);
			div1 = claim_element(div3_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			t2 = claim_text(div1_nodes, t2_value);
			div1_nodes.forEach(detach);
			t3 = claim_space(div3_nodes);
			div2 = claim_element(div3_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			t4 = claim_text(div2_nodes, t4_value);
			t5 = claim_text(div2_nodes, " - ");
			t6 = claim_text(div2_nodes, t6_value);
			div2_nodes.forEach(detach);
			t7 = claim_space(div3_nodes);
			if (if_block0) if_block0.l(div3_nodes);
			t8 = claim_space(div3_nodes);
			if (if_block1) if_block1.l(div3_nodes);
			t9 = claim_space(div3_nodes);
			div3_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(div0, "class", "calendar-name svelte-mr53e8");
			attr(div1, "class", "event-title svelte-mr53e8");
			attr(div2, "class", "event-time svelte-mr53e8");
			attr(div3, "class", "event svelte-mr53e8");
			set_style(div3, "border-color", /*event*/ ctx[2].calendar_color);
			this.first = div3;
		},
		m(target, anchor) {
			insert_hydration(target, div3, anchor);
			append_hydration(div3, div0);
			append_hydration(div0, t0);
			append_hydration(div3, t1);
			append_hydration(div3, div1);
			append_hydration(div1, t2);
			append_hydration(div3, t3);
			append_hydration(div3, div2);
			append_hydration(div2, t4);
			append_hydration(div2, t5);
			append_hydration(div2, t6);
			append_hydration(div3, t7);
			if (if_block0) if_block0.m(div3, null);
			append_hydration(div3, t8);
			if (if_block1) if_block1.m(div3, null);
			append_hydration(div3, t9);
		},
		p(new_ctx, dirty) {
			ctx = new_ctx;
			if (dirty & /*events*/ 1 && t0_value !== (t0_value = /*event*/ ctx[2].calendar_name + "")) set_data(t0, t0_value);
			if (dirty & /*events*/ 1 && t2_value !== (t2_value = /*event*/ ctx[2].title + "")) set_data(t2, t2_value);
			if (dirty & /*events*/ 1 && t4_value !== (t4_value = new Date(/*event*/ ctx[2].start * 1000).toLocaleString() + "")) set_data(t4, t4_value);
			if (dirty & /*events*/ 1 && t6_value !== (t6_value = new Date(/*event*/ ctx[2].end * 1000).toLocaleString() + "")) set_data(t6, t6_value);

			if (/*event*/ ctx[2].location) {
				if (if_block0) {
					if_block0.p(ctx, dirty);
				} else {
					if_block0 = create_if_block_2(ctx);
					if_block0.c();
					if_block0.m(div3, t8);
				}
			} else if (if_block0) {
				if_block0.d(1);
				if_block0 = null;
			}

			if (/*event*/ ctx[2].description) {
				if (if_block1) {
					if_block1.p(ctx, dirty);
				} else {
					if_block1 = create_if_block_1(ctx);
					if_block1.c();
					if_block1.m(div3, t9);
				}
			} else if (if_block1) {
				if_block1.d(1);
				if_block1 = null;
			}

			if (dirty & /*events*/ 1) {
				set_style(div3, "border-color", /*event*/ ctx[2].calendar_color);
			}
		},
		d(detaching) {
			if (detaching) detach(div3);
			if (if_block0) if_block0.d();
			if (if_block1) if_block1.d();
		}
	};
}

function create_fragment(ctx) {
	let div;

	function select_block_type(ctx, dirty) {
		if (/*events*/ ctx[0].length === 0) return create_if_block;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			div = element("div");
			if_block.c();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", {});
			var div_nodes = children(div);
			if_block.l(div_nodes);
			div_nodes.forEach(detach);
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			if_block.m(div, null);
		},
		p(ctx, [dirty]) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(div, null);
				}
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(div);
			if_block.d();
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { props } = $$props;
	let events = [];

	// Fetch the events on component mount
	onMount(async () => {
		//const response = await fetch("https://tmp.j7n.de/calendar/all.json");
		// events = await response.json();
		$$invalidate(0, events = [
			{
				"id": "ab2a63af-7863-4730-b947-5d2b488cedfd",
				"start": 1720522800,
				"end": 1720540800,
				"title": "Offenes Atelier Roddahn",
				"location": "Roddahn",
				"description": "kiri.li/studio",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "ab2a63af-7863-4730-b947-5d2b488cedfd",
				"start": 1720522800,
				"end": 1720540800,
				"title": "Offenes Atelier Roddahn",
				"location": "Roddahn",
				"description": "kiri.li/studio",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			},
			{
				"id": "2df7c966-afba-4358-97c4-97a2c8aa07e8",
				"start": 1720609200,
				"end": 1720627200,
				"title": "Offenes Atelier Roddahn",
				"location": "Roddahn",
				"description": "kiri.li/studio",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "2df7c966-afba-4358-97c4-97a2c8aa07e8",
				"start": 1720609200,
				"end": 1720627200,
				"title": "Offenes Atelier Roddahn",
				"location": "Roddahn",
				"description": "kiri.li/studio",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			},
			{
				"id": "40da66d0-e333-497f-b1b7-8f3dd6740d22",
				"start": 1720735200,
				"end": 1720994400,
				"title": "PPH: kulturFABRIKfest EIN STÜCK VOM GLÜCK",
				"description": "Theater / Musik / Zirkus / filmosophie / Kunstraum Turbnine / Workshops",
				"location": "Papierfabrik Hohenofen",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "40da66d0-e333-497f-b1b7-8f3dd6740d22",
				"start": 1720735200,
				"end": 1720994400,
				"title": "PPH: kulturFABRIKfest EIN STÜCK VOM GLÜCK",
				"description": "Theater / Musik / Zirkus / filmosophie / Kunstraum Turbnine / Workshops",
				"location": "Papierfabrik Hohenofen",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			},
			{
				"id": "0a4a90a0-207e-4ef8-bbd2-5f30107fabab",
				"start": 1721127600,
				"end": 1721145600,
				"title": "Offenes Atelier Roddahn",
				"location": "Roddahn",
				"description": "kiri.li/studio",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "0a4a90a0-207e-4ef8-bbd2-5f30107fabab",
				"start": 1721127600,
				"end": 1721145600,
				"title": "Offenes Atelier Roddahn",
				"location": "Roddahn",
				"description": "kiri.li/studio",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			},
			{
				"id": "8943a6ed-1bed-44ad-ac56-2dfa480735a7",
				"start": 1721214000,
				"end": 1721232000,
				"title": "Offenes Atelier Roddahn",
				"location": "Roddahn",
				"description": "kiri.li/studio",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "8943a6ed-1bed-44ad-ac56-2dfa480735a7",
				"start": 1721214000,
				"end": 1721232000,
				"title": "Offenes Atelier Roddahn",
				"location": "Roddahn",
				"description": "kiri.li/studio",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			},
			{
				"id": "f8d4aaee-007b-4bbf-ba66-596e18eb7b5c",
				"start": 1722031200,
				"end": 1722117600,
				"title": "PPH: Gastspiel Theaterkollektiv Tarantula: »Einsommernachtrstraum?«",
				"location": "Papierfabrik Hohenofen",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "f8d4aaee-007b-4bbf-ba66-596e18eb7b5c",
				"start": 1722031200,
				"end": 1722117600,
				"title": "PPH: Gastspiel Theaterkollektiv Tarantula: »Einsommernachtrstraum?«",
				"location": "Papierfabrik Hohenofen",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			},
			{
				"id": "c3583996-9dc0-4363-a901-6ca67e949f2c",
				"start": 1722204000,
				"end": 1722636000,
				"title": "PPH: Wir sind Welt(en)-Gestalter*innen",
				"description": "Kreativ-Workshop-Woche",
				"location": "Papierfabrik Hohenfoen",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "c3583996-9dc0-4363-a901-6ca67e949f2c",
				"start": 1722204000,
				"end": 1722636000,
				"title": "PPH: Wir sind Welt(en)-Gestalter*innen",
				"description": "Kreativ-Workshop-Woche",
				"location": "Papierfabrik Hohenfoen",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			},
			{
				"id": "161a4a6a-651b-4f8a-abc5-da130a229769",
				"start": 1722337200,
				"end": 1722355200,
				"title": "Offenes Atelier Roddahn",
				"location": "Roddahn",
				"description": "kiri.li/studio",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "161a4a6a-651b-4f8a-abc5-da130a229769",
				"start": 1722337200,
				"end": 1722355200,
				"title": "Offenes Atelier Roddahn",
				"location": "Roddahn",
				"description": "kiri.li/studio",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			},
			{
				"id": "a1d3cf3f-9ef6-4863-a8bc-e735b2599361",
				"start": 1722423600,
				"end": 1722441600,
				"title": "Offenes Atelier Roddahn",
				"location": "Roddahn",
				"description": "kiri.li/studio",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "a1d3cf3f-9ef6-4863-a8bc-e735b2599361",
				"start": 1722423600,
				"end": 1722441600,
				"title": "Offenes Atelier Roddahn",
				"location": "Roddahn",
				"description": "kiri.li/studio",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			},
			{
				"id": "6e2672d3-b006-4a7f-9b62-aacb0f1937c6",
				"start": 1722549600,
				"end": 1722636000,
				"title": "PPH: filmosophie",
				"location": "Papierfabrik Hohenofen",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "6e2672d3-b006-4a7f-9b62-aacb0f1937c6",
				"start": 1722549600,
				"end": 1722636000,
				"title": "PPH: filmosophie",
				"location": "Papierfabrik Hohenofen",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			},
			{
				"id": "7aa4866b-d43c-46a1-b91c-03f65842f81f",
				"start": 1722636000,
				"end": 1722722400,
				"title": "PPH: Vernissage Kunstraum Turbine",
				"description": "Gastspiel Laura Heinecke & Company: »HERTZ. Die Welt ist Schwingung«",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "7aa4866b-d43c-46a1-b91c-03f65842f81f",
				"start": 1722636000,
				"end": 1722722400,
				"title": "PPH: Vernissage Kunstraum Turbine",
				"description": "Gastspiel Laura Heinecke & Company: »HERTZ. Die Welt ist Schwingung«",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			},
			{
				"id": "fcd2efd9-522d-4b03-b5f3-1738beb6b0df",
				"start": 1723154400,
				"end": 1723413600,
				"title": "Festival Babe",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "fcd2efd9-522d-4b03-b5f3-1738beb6b0df",
				"start": 1723154400,
				"end": 1723413600,
				"title": "Festival Babe",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			},
			{
				"id": "f6e74558-4222-4c04-8780-4a339c9e01b1",
				"start": 1724277600,
				"end": 1724623200,
				"title": "Neiphos Festival",
				"location": "Damelack",
				"description": "https://neiphos.com",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "f6e74558-4222-4c04-8780-4a339c9e01b1",
				"start": 1724277600,
				"end": 1724623200,
				"title": "Neiphos Festival",
				"location": "Damelack",
				"description": "https://neiphos.com",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			},
			{
				"id": "d82c65bf-1a4f-4ee4-9dd8-cb27356c4aa2",
				"start": 1724623200,
				"end": 1725055200,
				"title": "PPH: Wir sind Welt(en)-Gestalter*innen",
				"description": "Zirkus-Workshop-Woche",
				"location": "Papierfabrik Hohenofen",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "d82c65bf-1a4f-4ee4-9dd8-cb27356c4aa2",
				"start": 1724623200,
				"end": 1725055200,
				"title": "PPH: Wir sind Welt(en)-Gestalter*innen",
				"description": "Zirkus-Workshop-Woche",
				"location": "Papierfabrik Hohenofen",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			},
			{
				"id": "297ff7b8-05ad-414a-95af-d1c3213ed223",
				"start": 1724968800,
				"end": 1725228000,
				"title": "PPH: ZIRKUS(S)machmitFESTIVAL",
				"description": "Zirkus / Feuershow / Musik / Theater / filmosophie / Kunstraum Turbine / Workshops",
				"location": "Papierfabrik Hohenofen",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "297ff7b8-05ad-414a-95af-d1c3213ed223",
				"start": 1724968800,
				"end": 1725228000,
				"title": "PPH: ZIRKUS(S)machmitFESTIVAL",
				"description": "Zirkus / Feuershow / Musik / Theater / filmosophie / Kunstraum Turbine / Workshops",
				"location": "Papierfabrik Hohenofen",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			},
			{
				"id": "a64e3fdf-21c0-4017-a1b9-2757bada9a86",
				"start": 1725573600,
				"end": 1725919200,
				"title": "Septre Festival",
				"location": "Damelack",
				"description": "www.septre.de",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "a64e3fdf-21c0-4017-a1b9-2757bada9a86",
				"start": 1725573600,
				"end": 1725919200,
				"title": "Septre Festival",
				"location": "Damelack",
				"description": "www.septre.de",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			},
			{
				"id": "ba3ac8db-799f-4b96-9fe1-8ff98daab208",
				"start": 1726783200,
				"end": 1727042400,
				"title": "Stüdyhaus Hoffest",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "ba3ac8db-799f-4b96-9fe1-8ff98daab208",
				"start": 1726783200,
				"end": 1727042400,
				"title": "Stüdyhaus Hoffest",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			},
			{
				"id": "65fb7ded-0932-42aa-84f9-ba4eb5b117aa",
				"start": 1726869600,
				"end": 1726956000,
				"title": "PPH: Vernissage Kunstraum Turbine",
				"location": "Papierfabrik Hohenofen",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "65fb7ded-0932-42aa-84f9-ba4eb5b117aa",
				"start": 1726869600,
				"end": 1726956000,
				"title": "PPH: Vernissage Kunstraum Turbine",
				"location": "Papierfabrik Hohenofen",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			},
			{
				"id": "c5e35f03-ad24-456a-ae87-1fb5be2fa678",
				"start": 1726956000,
				"end": 1727042400,
				"title": "PPH: Gastspiel Figurentheater Wilde & Vogel: »überALL unterALL«",
				"location": "Papierfabrik Hohenofen",
				"description": "Wir sind Welt(en)-Gestalter*innen Kreativ-Workshop",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "c5e35f03-ad24-456a-ae87-1fb5be2fa678",
				"start": 1726956000,
				"end": 1727042400,
				"title": "PPH: Gastspiel Figurentheater Wilde & Vogel: »überALL unterALL«",
				"location": "Papierfabrik Hohenofen",
				"description": "Wir sind Welt(en)-Gestalter*innen Kreativ-Workshop",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			},
			{
				"id": "68af32d1-8fe5-4f29-8814-dfc6d4de16c8",
				"start": 1728684000,
				"end": 1728770400,
				"title": "PPH: nebenanFABRIK",
				"location": "Papierfabrik Hohenofen",
				"description": "Kulturprogramm / Begegenung",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "68af32d1-8fe5-4f29-8814-dfc6d4de16c8",
				"start": 1728684000,
				"end": 1728770400,
				"title": "PPH: nebenanFABRIK",
				"location": "Papierfabrik Hohenofen",
				"description": "Kulturprogramm / Begegenung",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			},
			{
				"id": "8d219874-0681-48c1-b4c5-116a4d5a3ab2",
				"start": 1733007600,
				"end": 1733094000,
				"title": "PPH: lichtFabrik",
				"location": "Papierfabrik Hohenofen",
				"description": "Kulturprogramm / Adventsmarkt",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "8d219874-0681-48c1-b4c5-116a4d5a3ab2",
				"start": 1733007600,
				"end": 1733094000,
				"title": "PPH: lichtFabrik",
				"location": "Papierfabrik Hohenofen",
				"description": "Kulturprogramm / Adventsmarkt",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			},
			{
				"id": "6f111fd9-ee44-4b8c-99f4-3cd74422a5d6",
				"start": 1735945200,
				"end": 1736031600,
				"title": "Test",
				"calendar_name": "Calendar 1",
				"calendar_color": "#FF5733"
			},
			{
				"id": "6f111fd9-ee44-4b8c-99f4-3cd74422a5d6",
				"start": 1735945200,
				"end": 1736031600,
				"title": "Test",
				"calendar_name": "Calendar 2",
				"calendar_color": "#33FF57"
			}
		]);
	});

	$$self.$$set = $$props => {
		if ('props' in $$props) $$invalidate(1, props = $$props.props);
	};

	return [events, props];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { props: 1 });
	}
}

export { Component as default };
