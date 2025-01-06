// Hero with form - Updated January 6, 2025
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
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
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

const exports = {}; const module = { exports };

!function(e,t){"object"==typeof exports&&"undefined"!=typeof module?module.exports=t():"function"==typeof define&&define.amd?define(t):(e="undefined"!=typeof globalThis?globalThis:e||self).axios=t();}(undefined,(function(){function e(e){var r,n;function o(r,n){try{var a=e[r](n),u=a.value,s=u instanceof t;Promise.resolve(s?u.v:u).then((function(t){if(s){var n="return"===r?"return":"next";if(!u.k||t.done)return o(n,t);t=e[n](t).value;}i(a.done?"return":"normal",t);}),(function(e){o("throw",e);}));}catch(e){i("throw",e);}}function i(e,t){switch(e){case"return":r.resolve({value:t,done:!0});break;case"throw":r.reject(t);break;default:r.resolve({value:t,done:!1});}(r=r.next)?o(r.key,r.arg):n=null;}this._invoke=function(e,t){return new Promise((function(i,a){var u={key:e,arg:t,resolve:i,reject:a,next:null};n?n=n.next=u:(r=n=u,o(e,t));}))},"function"!=typeof e.return&&(this.return=void 0);}function t(e,t){this.v=e,this.k=t;}function r(e){var r={},n=!1;function o(r,o){return n=!0,o=new Promise((function(t){t(e[r](o));})),{done:!1,value:new t(o,1)}}return r["undefined"!=typeof Symbol&&Symbol.iterator||"@@iterator"]=function(){return this},r.next=function(e){return n?(n=!1,e):o("next",e)},"function"==typeof e.throw&&(r.throw=function(e){if(n)throw n=!1,e;return o("throw",e)}),"function"==typeof e.return&&(r.return=function(e){return n?(n=!1,e):o("return",e)}),r}function n(e){var t,r,n,i=2;for("undefined"!=typeof Symbol&&(r=Symbol.asyncIterator,n=Symbol.iterator);i--;){if(r&&null!=(t=e[r]))return t.call(e);if(n&&null!=(t=e[n]))return new o(t.call(e));r="@@asyncIterator",n="@@iterator";}throw new TypeError("Object is not async iterable")}function o(e){function t(e){if(Object(e)!==e)return Promise.reject(new TypeError(e+" is not an object."));var t=e.done;return Promise.resolve(e.value).then((function(e){return {value:e,done:t}}))}return o=function(e){this.s=e,this.n=e.next;},o.prototype={s:null,n:null,next:function(){return t(this.n.apply(this.s,arguments))},return:function(e){var r=this.s.return;return void 0===r?Promise.resolve({value:e,done:!0}):t(r.apply(this.s,arguments))},throw:function(e){var r=this.s.return;return void 0===r?Promise.reject(e):t(r.apply(this.s,arguments))}},new o(e)}function i(e){return new t(e,0)}function a(e,t){var r=Object.keys(e);if(Object.getOwnPropertySymbols){var n=Object.getOwnPropertySymbols(e);t&&(n=n.filter((function(t){return Object.getOwnPropertyDescriptor(e,t).enumerable}))),r.push.apply(r,n);}return r}function u(e){for(var t=1;t<arguments.length;t++){var r=null!=arguments[t]?arguments[t]:{};t%2?a(Object(r),!0).forEach((function(t){m(e,t,r[t]);})):Object.getOwnPropertyDescriptors?Object.defineProperties(e,Object.getOwnPropertyDescriptors(r)):a(Object(r)).forEach((function(t){Object.defineProperty(e,t,Object.getOwnPropertyDescriptor(r,t));}));}return e}function s(){s=function(){return t};var e,t={},r=Object.prototype,n=r.hasOwnProperty,o=Object.defineProperty||function(e,t,r){e[t]=r.value;},i="function"==typeof Symbol?Symbol:{},a=i.iterator||"@@iterator",u=i.asyncIterator||"@@asyncIterator",c=i.toStringTag||"@@toStringTag";function f(e,t,r){return Object.defineProperty(e,t,{value:r,enumerable:!0,configurable:!0,writable:!0}),e[t]}try{f({},"");}catch(e){f=function(e,t,r){return e[t]=r};}function l(e,t,r,n){var i=t&&t.prototype instanceof m?t:m,a=Object.create(i.prototype),u=new P(n||[]);return o(a,"_invoke",{value:T(e,r,u)}),a}function p(e,t,r){try{return {type:"normal",arg:e.call(t,r)}}catch(e){return {type:"throw",arg:e}}}t.wrap=l;var h="suspendedStart",d="executing",v="completed",y={};function m(){}function b(){}function g(){}var w={};f(w,a,(function(){return this}));var E=Object.getPrototypeOf,O=E&&E(E(L([])));O&&O!==r&&n.call(O,a)&&(w=O);var S=g.prototype=m.prototype=Object.create(w);function x(e){["next","throw","return"].forEach((function(t){f(e,t,(function(e){return this._invoke(t,e)}));}));}function R(e,t){function r(o,i,a,u){var s=p(e[o],e,i);if("throw"!==s.type){var c=s.arg,f=c.value;return f&&"object"==typeof f&&n.call(f,"__await")?t.resolve(f.__await).then((function(e){r("next",e,a,u);}),(function(e){r("throw",e,a,u);})):t.resolve(f).then((function(e){c.value=e,a(c);}),(function(e){return r("throw",e,a,u)}))}u(s.arg);}var i;o(this,"_invoke",{value:function(e,n){function o(){return new t((function(t,o){r(e,n,t,o);}))}return i=i?i.then(o,o):o()}});}function T(t,r,n){var o=h;return function(i,a){if(o===d)throw new Error("Generator is already running");if(o===v){if("throw"===i)throw a;return {value:e,done:!0}}for(n.method=i,n.arg=a;;){var u=n.delegate;if(u){var s=k(u,n);if(s){if(s===y)continue;return s}}if("next"===n.method)n.sent=n._sent=n.arg;else if("throw"===n.method){if(o===h)throw o=v,n.arg;n.dispatchException(n.arg);}else "return"===n.method&&n.abrupt("return",n.arg);o=d;var c=p(t,r,n);if("normal"===c.type){if(o=n.done?v:"suspendedYield",c.arg===y)continue;return {value:c.arg,done:n.done}}"throw"===c.type&&(o=v,n.method="throw",n.arg=c.arg);}}}function k(t,r){var n=r.method,o=t.iterator[n];if(o===e)return r.delegate=null,"throw"===n&&t.iterator.return&&(r.method="return",r.arg=e,k(t,r),"throw"===r.method)||"return"!==n&&(r.method="throw",r.arg=new TypeError("The iterator does not provide a '"+n+"' method")),y;var i=p(o,t.iterator,r.arg);if("throw"===i.type)return r.method="throw",r.arg=i.arg,r.delegate=null,y;var a=i.arg;return a?a.done?(r[t.resultName]=a.value,r.next=t.nextLoc,"return"!==r.method&&(r.method="next",r.arg=e),r.delegate=null,y):a:(r.method="throw",r.arg=new TypeError("iterator result is not an object"),r.delegate=null,y)}function j(e){var t={tryLoc:e[0]};1 in e&&(t.catchLoc=e[1]),2 in e&&(t.finallyLoc=e[2],t.afterLoc=e[3]),this.tryEntries.push(t);}function A(e){var t=e.completion||{};t.type="normal",delete t.arg,e.completion=t;}function P(e){this.tryEntries=[{tryLoc:"root"}],e.forEach(j,this),this.reset(!0);}function L(t){if(t||""===t){var r=t[a];if(r)return r.call(t);if("function"==typeof t.next)return t;if(!isNaN(t.length)){var o=-1,i=function r(){for(;++o<t.length;)if(n.call(t,o))return r.value=t[o],r.done=!1,r;return r.value=e,r.done=!0,r};return i.next=i}}throw new TypeError(typeof t+" is not iterable")}return b.prototype=g,o(S,"constructor",{value:g,configurable:!0}),o(g,"constructor",{value:b,configurable:!0}),b.displayName=f(g,c,"GeneratorFunction"),t.isGeneratorFunction=function(e){var t="function"==typeof e&&e.constructor;return !!t&&(t===b||"GeneratorFunction"===(t.displayName||t.name))},t.mark=function(e){return Object.setPrototypeOf?Object.setPrototypeOf(e,g):(e.__proto__=g,f(e,c,"GeneratorFunction")),e.prototype=Object.create(S),e},t.awrap=function(e){return {__await:e}},x(R.prototype),f(R.prototype,u,(function(){return this})),t.AsyncIterator=R,t.async=function(e,r,n,o,i){void 0===i&&(i=Promise);var a=new R(l(e,r,n,o),i);return t.isGeneratorFunction(r)?a:a.next().then((function(e){return e.done?e.value:a.next()}))},x(S),f(S,c,"Generator"),f(S,a,(function(){return this})),f(S,"toString",(function(){return "[object Generator]"})),t.keys=function(e){var t=Object(e),r=[];for(var n in t)r.push(n);return r.reverse(),function e(){for(;r.length;){var n=r.pop();if(n in t)return e.value=n,e.done=!1,e}return e.done=!0,e}},t.values=L,P.prototype={constructor:P,reset:function(t){if(this.prev=0,this.next=0,this.sent=this._sent=e,this.done=!1,this.delegate=null,this.method="next",this.arg=e,this.tryEntries.forEach(A),!t)for(var r in this)"t"===r.charAt(0)&&n.call(this,r)&&!isNaN(+r.slice(1))&&(this[r]=e);},stop:function(){this.done=!0;var e=this.tryEntries[0].completion;if("throw"===e.type)throw e.arg;return this.rval},dispatchException:function(t){if(this.done)throw t;var r=this;function o(n,o){return u.type="throw",u.arg=t,r.next=n,o&&(r.method="next",r.arg=e),!!o}for(var i=this.tryEntries.length-1;i>=0;--i){var a=this.tryEntries[i],u=a.completion;if("root"===a.tryLoc)return o("end");if(a.tryLoc<=this.prev){var s=n.call(a,"catchLoc"),c=n.call(a,"finallyLoc");if(s&&c){if(this.prev<a.catchLoc)return o(a.catchLoc,!0);if(this.prev<a.finallyLoc)return o(a.finallyLoc)}else if(s){if(this.prev<a.catchLoc)return o(a.catchLoc,!0)}else {if(!c)throw new Error("try statement without catch or finally");if(this.prev<a.finallyLoc)return o(a.finallyLoc)}}}},abrupt:function(e,t){for(var r=this.tryEntries.length-1;r>=0;--r){var o=this.tryEntries[r];if(o.tryLoc<=this.prev&&n.call(o,"finallyLoc")&&this.prev<o.finallyLoc){var i=o;break}}i&&("break"===e||"continue"===e)&&i.tryLoc<=t&&t<=i.finallyLoc&&(i=null);var a=i?i.completion:{};return a.type=e,a.arg=t,i?(this.method="next",this.next=i.finallyLoc,y):this.complete(a)},complete:function(e,t){if("throw"===e.type)throw e.arg;return "break"===e.type||"continue"===e.type?this.next=e.arg:"return"===e.type?(this.rval=this.arg=e.arg,this.method="return",this.next="end"):"normal"===e.type&&t&&(this.next=t),y},finish:function(e){for(var t=this.tryEntries.length-1;t>=0;--t){var r=this.tryEntries[t];if(r.finallyLoc===e)return this.complete(r.completion,r.afterLoc),A(r),y}},catch:function(e){for(var t=this.tryEntries.length-1;t>=0;--t){var r=this.tryEntries[t];if(r.tryLoc===e){var n=r.completion;if("throw"===n.type){var o=n.arg;A(r);}return o}}throw new Error("illegal catch attempt")},delegateYield:function(t,r,n){return this.delegate={iterator:L(t),resultName:r,nextLoc:n},"next"===this.method&&(this.arg=e),y}},t}function c(e){var t=function(e,t){if("object"!=typeof e||!e)return e;var r=e[Symbol.toPrimitive];if(void 0!==r){var n=r.call(e,t||"default");if("object"!=typeof n)return n;throw new TypeError("@@toPrimitive must return a primitive value.")}return ("string"===t?String:Number)(e)}(e,"string");return "symbol"==typeof t?t:String(t)}function f(e){return f="function"==typeof Symbol&&"symbol"==typeof Symbol.iterator?function(e){return typeof e}:function(e){return e&&"function"==typeof Symbol&&e.constructor===Symbol&&e!==Symbol.prototype?"symbol":typeof e},f(e)}function l(t){return function(){return new e(t.apply(this,arguments))}}function p(e,t,r,n,o,i,a){try{var u=e[i](a),s=u.value;}catch(e){return void r(e)}u.done?t(s):Promise.resolve(s).then(n,o);}function h(e){return function(){var t=this,r=arguments;return new Promise((function(n,o){var i=e.apply(t,r);function a(e){p(i,n,o,a,u,"next",e);}function u(e){p(i,n,o,a,u,"throw",e);}a(void 0);}))}}function d(e,t){if(!(e instanceof t))throw new TypeError("Cannot call a class as a function")}function v(e,t){for(var r=0;r<t.length;r++){var n=t[r];n.enumerable=n.enumerable||!1,n.configurable=!0,"value"in n&&(n.writable=!0),Object.defineProperty(e,c(n.key),n);}}function y(e,t,r){return t&&v(e.prototype,t),r&&v(e,r),Object.defineProperty(e,"prototype",{writable:!1}),e}function m(e,t,r){return (t=c(t))in e?Object.defineProperty(e,t,{value:r,enumerable:!0,configurable:!0,writable:!0}):e[t]=r,e}function b(e,t){return w(e)||function(e,t){var r=null==e?null:"undefined"!=typeof Symbol&&e[Symbol.iterator]||e["@@iterator"];if(null!=r){var n,o,i,a,u=[],s=!0,c=!1;try{if(i=(r=r.call(e)).next,0===t){if(Object(r)!==r)return;s=!1;}else for(;!(s=(n=i.call(r)).done)&&(u.push(n.value),u.length!==t);s=!0);}catch(e){c=!0,o=e;}finally{try{if(!s&&null!=r.return&&(a=r.return(),Object(a)!==a))return}finally{if(c)throw o}}return u}}(e,t)||O(e,t)||x()}function g(e){return function(e){if(Array.isArray(e))return S(e)}(e)||E(e)||O(e)||function(){throw new TypeError("Invalid attempt to spread non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method.")}()}function w(e){if(Array.isArray(e))return e}function E(e){if("undefined"!=typeof Symbol&&null!=e[Symbol.iterator]||null!=e["@@iterator"])return Array.from(e)}function O(e,t){if(e){if("string"==typeof e)return S(e,t);var r=Object.prototype.toString.call(e).slice(8,-1);return "Object"===r&&e.constructor&&(r=e.constructor.name),"Map"===r||"Set"===r?Array.from(e):"Arguments"===r||/^(?:Ui|I)nt(?:8|16|32)(?:Clamped)?Array$/.test(r)?S(e,t):void 0}}function S(e,t){(null==t||t>e.length)&&(t=e.length);for(var r=0,n=new Array(t);r<t;r++)n[r]=e[r];return n}function x(){throw new TypeError("Invalid attempt to destructure non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method.")}function R(e,t){return function(){return e.apply(t,arguments)}}e.prototype["function"==typeof Symbol&&Symbol.asyncIterator||"@@asyncIterator"]=function(){return this},e.prototype.next=function(e){return this._invoke("next",e)},e.prototype.throw=function(e){return this._invoke("throw",e)},e.prototype.return=function(e){return this._invoke("return",e)};var T,k=Object.prototype.toString,j=Object.getPrototypeOf,A=(T=Object.create(null),function(e){var t=k.call(e);return T[t]||(T[t]=t.slice(8,-1).toLowerCase())}),P=function(e){return e=e.toLowerCase(),function(t){return A(t)===e}},L=function(e){return function(t){return f(t)===e}},N=Array.isArray,_=L("undefined");var C=P("ArrayBuffer");var F=L("string"),U=L("function"),B=L("number"),D=function(e){return null!==e&&"object"===f(e)},I=function(e){if("object"!==A(e))return !1;var t=j(e);return !(null!==t&&t!==Object.prototype&&null!==Object.getPrototypeOf(t)||Symbol.toStringTag in e||Symbol.iterator in e)},q=P("Date"),M=P("File"),z=P("Blob"),H=P("FileList"),J=P("URLSearchParams"),W=b(["ReadableStream","Request","Response","Headers"].map(P),4),G=W[0],K=W[1],V=W[2],X=W[3];function $(e,t){var r,n,o=arguments.length>2&&void 0!==arguments[2]?arguments[2]:{},i=o.allOwnKeys,a=void 0!==i&&i;if(null!=e)if("object"!==f(e)&&(e=[e]),N(e))for(r=0,n=e.length;r<n;r++)t.call(null,e[r],r,e);else {var u,s=a?Object.getOwnPropertyNames(e):Object.keys(e),c=s.length;for(r=0;r<c;r++)u=s[r],t.call(null,e[u],u,e);}}function Y(e,t){t=t.toLowerCase();for(var r,n=Object.keys(e),o=n.length;o-- >0;)if(t===(r=n[o]).toLowerCase())return r;return null}var Q="undefined"!=typeof globalThis?globalThis:"undefined"!=typeof self?self:"undefined"!=typeof window?window:global,Z=function(e){return !_(e)&&e!==Q};var ee,te=(ee="undefined"!=typeof Uint8Array&&j(Uint8Array),function(e){return ee&&e instanceof ee}),re=P("HTMLFormElement"),ne=function(e){var t=Object.prototype.hasOwnProperty;return function(e,r){return t.call(e,r)}}(),oe=P("RegExp"),ie=function(e,t){var r=Object.getOwnPropertyDescriptors(e),n={};$(r,(function(r,o){var i;!1!==(i=t(r,o,e))&&(n[o]=i||r);})),Object.defineProperties(e,n);},ae="abcdefghijklmnopqrstuvwxyz",ue="0123456789",se={DIGIT:ue,ALPHA:ae,ALPHA_DIGIT:ae+ae.toUpperCase()+ue};var ce,fe,le,pe,he=P("AsyncFunction"),de=(ce="function"==typeof setImmediate,fe=U(Q.postMessage),ce?setImmediate:fe?(le="axios@".concat(Math.random()),pe=[],Q.addEventListener("message",(function(e){var t=e.source,r=e.data;t===Q&&r===le&&pe.length&&pe.shift()();}),!1),function(e){pe.push(e),Q.postMessage(le,"*");}):function(e){return setTimeout(e)}),ve="undefined"!=typeof queueMicrotask?queueMicrotask.bind(Q):"undefined"!=typeof process&&process.nextTick||de,ye={isArray:N,isArrayBuffer:C,isBuffer:function(e){return null!==e&&!_(e)&&null!==e.constructor&&!_(e.constructor)&&U(e.constructor.isBuffer)&&e.constructor.isBuffer(e)},isFormData:function(e){var t;return e&&("function"==typeof FormData&&e instanceof FormData||U(e.append)&&("formdata"===(t=A(e))||"object"===t&&U(e.toString)&&"[object FormData]"===e.toString()))},isArrayBufferView:function(e){return "undefined"!=typeof ArrayBuffer&&ArrayBuffer.isView?ArrayBuffer.isView(e):e&&e.buffer&&C(e.buffer)},isString:F,isNumber:B,isBoolean:function(e){return !0===e||!1===e},isObject:D,isPlainObject:I,isReadableStream:G,isRequest:K,isResponse:V,isHeaders:X,isUndefined:_,isDate:q,isFile:M,isBlob:z,isRegExp:oe,isFunction:U,isStream:function(e){return D(e)&&U(e.pipe)},isURLSearchParams:J,isTypedArray:te,isFileList:H,forEach:$,merge:function e(){for(var t=Z(this)&&this||{},r=t.caseless,n={},o=function(t,o){var i=r&&Y(n,o)||o;I(n[i])&&I(t)?n[i]=e(n[i],t):I(t)?n[i]=e({},t):N(t)?n[i]=t.slice():n[i]=t;},i=0,a=arguments.length;i<a;i++)arguments[i]&&$(arguments[i],o);return n},extend:function(e,t,r){var n=arguments.length>3&&void 0!==arguments[3]?arguments[3]:{},o=n.allOwnKeys;return $(t,(function(t,n){r&&U(t)?e[n]=R(t,r):e[n]=t;}),{allOwnKeys:o}),e},trim:function(e){return e.trim?e.trim():e.replace(/^[\s\uFEFF\xA0]+|[\s\uFEFF\xA0]+$/g,"")},stripBOM:function(e){return 65279===e.charCodeAt(0)&&(e=e.slice(1)),e},inherits:function(e,t,r,n){e.prototype=Object.create(t.prototype,n),e.prototype.constructor=e,Object.defineProperty(e,"super",{value:t.prototype}),r&&Object.assign(e.prototype,r);},toFlatObject:function(e,t,r,n){var o,i,a,u={};if(t=t||{},null==e)return t;do{for(i=(o=Object.getOwnPropertyNames(e)).length;i-- >0;)a=o[i],n&&!n(a,e,t)||u[a]||(t[a]=e[a],u[a]=!0);e=!1!==r&&j(e);}while(e&&(!r||r(e,t))&&e!==Object.prototype);return t},kindOf:A,kindOfTest:P,endsWith:function(e,t,r){e=String(e),(void 0===r||r>e.length)&&(r=e.length),r-=t.length;var n=e.indexOf(t,r);return -1!==n&&n===r},toArray:function(e){if(!e)return null;if(N(e))return e;var t=e.length;if(!B(t))return null;for(var r=new Array(t);t-- >0;)r[t]=e[t];return r},forEachEntry:function(e,t){for(var r,n=(e&&e[Symbol.iterator]).call(e);(r=n.next())&&!r.done;){var o=r.value;t.call(e,o[0],o[1]);}},matchAll:function(e,t){for(var r,n=[];null!==(r=e.exec(t));)n.push(r);return n},isHTMLForm:re,hasOwnProperty:ne,hasOwnProp:ne,reduceDescriptors:ie,freezeMethods:function(e){ie(e,(function(t,r){if(U(e)&&-1!==["arguments","caller","callee"].indexOf(r))return !1;var n=e[r];U(n)&&(t.enumerable=!1,"writable"in t?t.writable=!1:t.set||(t.set=function(){throw Error("Can not rewrite read-only method '"+r+"'")}));}));},toObjectSet:function(e,t){var r={},n=function(e){e.forEach((function(e){r[e]=!0;}));};return N(e)?n(e):n(String(e).split(t)),r},toCamelCase:function(e){return e.toLowerCase().replace(/[-_\s]([a-z\d])(\w*)/g,(function(e,t,r){return t.toUpperCase()+r}))},noop:function(){},toFiniteNumber:function(e,t){return null!=e&&Number.isFinite(e=+e)?e:t},findKey:Y,global:Q,isContextDefined:Z,ALPHABET:se,generateString:function(){for(var e=arguments.length>0&&void 0!==arguments[0]?arguments[0]:16,t=arguments.length>1&&void 0!==arguments[1]?arguments[1]:se.ALPHA_DIGIT,r="",n=t.length;e--;)r+=t[Math.random()*n|0];return r},isSpecCompliantForm:function(e){return !!(e&&U(e.append)&&"FormData"===e[Symbol.toStringTag]&&e[Symbol.iterator])},toJSONObject:function(e){var t=new Array(10);return function e(r,n){if(D(r)){if(t.indexOf(r)>=0)return;if(!("toJSON"in r)){t[n]=r;var o=N(r)?[]:{};return $(r,(function(t,r){var i=e(t,n+1);!_(i)&&(o[r]=i);})),t[n]=void 0,o}}return r}(e,0)},isAsyncFn:he,isThenable:function(e){return e&&(D(e)||U(e))&&U(e.then)&&U(e.catch)},setImmediate:de,asap:ve};function me(e,t,r,n,o){Error.call(this),Error.captureStackTrace?Error.captureStackTrace(this,this.constructor):this.stack=(new Error).stack,this.message=e,this.name="AxiosError",t&&(this.code=t),r&&(this.config=r),n&&(this.request=n),o&&(this.response=o,this.status=o.status?o.status:null);}ye.inherits(me,Error,{toJSON:function(){return {message:this.message,name:this.name,description:this.description,number:this.number,fileName:this.fileName,lineNumber:this.lineNumber,columnNumber:this.columnNumber,stack:this.stack,config:ye.toJSONObject(this.config),code:this.code,status:this.status}}});var be=me.prototype,ge={};["ERR_BAD_OPTION_VALUE","ERR_BAD_OPTION","ECONNABORTED","ETIMEDOUT","ERR_NETWORK","ERR_FR_TOO_MANY_REDIRECTS","ERR_DEPRECATED","ERR_BAD_RESPONSE","ERR_BAD_REQUEST","ERR_CANCELED","ERR_NOT_SUPPORT","ERR_INVALID_URL"].forEach((function(e){ge[e]={value:e};})),Object.defineProperties(me,ge),Object.defineProperty(be,"isAxiosError",{value:!0}),me.from=function(e,t,r,n,o,i){var a=Object.create(be);return ye.toFlatObject(e,a,(function(e){return e!==Error.prototype}),(function(e){return "isAxiosError"!==e})),me.call(a,e.message,t,r,n,o),a.cause=e,a.name=e.name,i&&Object.assign(a,i),a};function we(e){return ye.isPlainObject(e)||ye.isArray(e)}function Ee(e){return ye.endsWith(e,"[]")?e.slice(0,-2):e}function Oe(e,t,r){return e?e.concat(t).map((function(e,t){return e=Ee(e),!r&&t?"["+e+"]":e})).join(r?".":""):t}var Se=ye.toFlatObject(ye,{},null,(function(e){return /^is[A-Z]/.test(e)}));function xe(e,t,r){if(!ye.isObject(e))throw new TypeError("target must be an object");t=t||new FormData;var n=(r=ye.toFlatObject(r,{metaTokens:!0,dots:!1,indexes:!1},!1,(function(e,t){return !ye.isUndefined(t[e])}))).metaTokens,o=r.visitor||c,i=r.dots,a=r.indexes,u=(r.Blob||"undefined"!=typeof Blob&&Blob)&&ye.isSpecCompliantForm(t);if(!ye.isFunction(o))throw new TypeError("visitor must be a function");function s(e){if(null===e)return "";if(ye.isDate(e))return e.toISOString();if(!u&&ye.isBlob(e))throw new me("Blob is not supported. Use a Buffer instead.");return ye.isArrayBuffer(e)||ye.isTypedArray(e)?u&&"function"==typeof Blob?new Blob([e]):Buffer.from(e):e}function c(e,r,o){var u=e;if(e&&!o&&"object"===f(e))if(ye.endsWith(r,"{}"))r=n?r:r.slice(0,-2),e=JSON.stringify(e);else if(ye.isArray(e)&&function(e){return ye.isArray(e)&&!e.some(we)}(e)||(ye.isFileList(e)||ye.endsWith(r,"[]"))&&(u=ye.toArray(e)))return r=Ee(r),u.forEach((function(e,n){!ye.isUndefined(e)&&null!==e&&t.append(!0===a?Oe([r],n,i):null===a?r:r+"[]",s(e));})),!1;return !!we(e)||(t.append(Oe(o,r,i),s(e)),!1)}var l=[],p=Object.assign(Se,{defaultVisitor:c,convertValue:s,isVisitable:we});if(!ye.isObject(e))throw new TypeError("data must be an object");return function e(r,n){if(!ye.isUndefined(r)){if(-1!==l.indexOf(r))throw Error("Circular reference detected in "+n.join("."));l.push(r),ye.forEach(r,(function(r,i){!0===(!(ye.isUndefined(r)||null===r)&&o.call(t,r,ye.isString(i)?i.trim():i,n,p))&&e(r,n?n.concat(i):[i]);})),l.pop();}}(e),t}function Re(e){var t={"!":"%21","'":"%27","(":"%28",")":"%29","~":"%7E","%20":"+","%00":"\0"};return encodeURIComponent(e).replace(/[!'()~]|%20|%00/g,(function(e){return t[e]}))}function Te(e,t){this._pairs=[],e&&xe(e,this,t);}var ke=Te.prototype;function je(e){return encodeURIComponent(e).replace(/%3A/gi,":").replace(/%24/g,"$").replace(/%2C/gi,",").replace(/%20/g,"+").replace(/%5B/gi,"[").replace(/%5D/gi,"]")}function Ae(e,t,r){if(!t)return e;var n=r&&r.encode||je;ye.isFunction(r)&&(r={serialize:r});var o,i=r&&r.serialize;if(o=i?i(t,r):ye.isURLSearchParams(t)?t.toString():new Te(t,r).toString(n)){var a=e.indexOf("#");-1!==a&&(e=e.slice(0,a)),e+=(-1===e.indexOf("?")?"?":"&")+o;}return e}ke.append=function(e,t){this._pairs.push([e,t]);},ke.toString=function(e){var t=e?function(t){return e.call(this,t,Re)}:Re;return this._pairs.map((function(e){return t(e[0])+"="+t(e[1])}),"").join("&")};var Pe=function(){function e(){d(this,e),this.handlers=[];}return y(e,[{key:"use",value:function(e,t,r){return this.handlers.push({fulfilled:e,rejected:t,synchronous:!!r&&r.synchronous,runWhen:r?r.runWhen:null}),this.handlers.length-1}},{key:"eject",value:function(e){this.handlers[e]&&(this.handlers[e]=null);}},{key:"clear",value:function(){this.handlers&&(this.handlers=[]);}},{key:"forEach",value:function(e){ye.forEach(this.handlers,(function(t){null!==t&&e(t);}));}}]),e}(),Le={silentJSONParsing:!0,forcedJSONParsing:!0,clarifyTimeoutError:!1},Ne={isBrowser:!0,classes:{URLSearchParams:"undefined"!=typeof URLSearchParams?URLSearchParams:Te,FormData:"undefined"!=typeof FormData?FormData:null,Blob:"undefined"!=typeof Blob?Blob:null},protocols:["http","https","file","blob","url","data"]},_e="undefined"!=typeof window&&"undefined"!=typeof document,Ce="object"===("undefined"==typeof navigator?"undefined":f(navigator))&&navigator||void 0,Fe=_e&&(!Ce||["ReactNative","NativeScript","NS"].indexOf(Ce.product)<0),Ue="undefined"!=typeof WorkerGlobalScope&&self instanceof WorkerGlobalScope&&"function"==typeof self.importScripts,Be=_e&&window.location.href||"http://localhost",De=u(u({},Object.freeze({__proto__:null,hasBrowserEnv:_e,hasStandardBrowserWebWorkerEnv:Ue,hasStandardBrowserEnv:Fe,navigator:Ce,origin:Be})),Ne);function Ie(e){function t(e,r,n,o){var i=e[o++];if("__proto__"===i)return !0;var a=Number.isFinite(+i),u=o>=e.length;return i=!i&&ye.isArray(n)?n.length:i,u?(ye.hasOwnProp(n,i)?n[i]=[n[i],r]:n[i]=r,!a):(n[i]&&ye.isObject(n[i])||(n[i]=[]),t(e,r,n[i],o)&&ye.isArray(n[i])&&(n[i]=function(e){var t,r,n={},o=Object.keys(e),i=o.length;for(t=0;t<i;t++)n[r=o[t]]=e[r];return n}(n[i])),!a)}if(ye.isFormData(e)&&ye.isFunction(e.entries)){var r={};return ye.forEachEntry(e,(function(e,n){t(function(e){return ye.matchAll(/\w+|\[(\w*)]/g,e).map((function(e){return "[]"===e[0]?"":e[1]||e[0]}))}(e),n,r,0);})),r}return null}var qe={transitional:Le,adapter:["xhr","http","fetch"],transformRequest:[function(e,t){var r,n=t.getContentType()||"",o=n.indexOf("application/json")>-1,i=ye.isObject(e);if(i&&ye.isHTMLForm(e)&&(e=new FormData(e)),ye.isFormData(e))return o?JSON.stringify(Ie(e)):e;if(ye.isArrayBuffer(e)||ye.isBuffer(e)||ye.isStream(e)||ye.isFile(e)||ye.isBlob(e)||ye.isReadableStream(e))return e;if(ye.isArrayBufferView(e))return e.buffer;if(ye.isURLSearchParams(e))return t.setContentType("application/x-www-form-urlencoded;charset=utf-8",!1),e.toString();if(i){if(n.indexOf("application/x-www-form-urlencoded")>-1)return function(e,t){return xe(e,new De.classes.URLSearchParams,Object.assign({visitor:function(e,t,r,n){return De.isNode&&ye.isBuffer(e)?(this.append(t,e.toString("base64")),!1):n.defaultVisitor.apply(this,arguments)}},t))}(e,this.formSerializer).toString();if((r=ye.isFileList(e))||n.indexOf("multipart/form-data")>-1){var a=this.env&&this.env.FormData;return xe(r?{"files[]":e}:e,a&&new a,this.formSerializer)}}return i||o?(t.setContentType("application/json",!1),function(e,t,r){if(ye.isString(e))try{return (t||JSON.parse)(e),ye.trim(e)}catch(e){if("SyntaxError"!==e.name)throw e}return (r||JSON.stringify)(e)}(e)):e}],transformResponse:[function(e){var t=this.transitional||qe.transitional,r=t&&t.forcedJSONParsing,n="json"===this.responseType;if(ye.isResponse(e)||ye.isReadableStream(e))return e;if(e&&ye.isString(e)&&(r&&!this.responseType||n)){var o=!(t&&t.silentJSONParsing)&&n;try{return JSON.parse(e)}catch(e){if(o){if("SyntaxError"===e.name)throw me.from(e,me.ERR_BAD_RESPONSE,this,null,this.response);throw e}}}return e}],timeout:0,xsrfCookieName:"XSRF-TOKEN",xsrfHeaderName:"X-XSRF-TOKEN",maxContentLength:-1,maxBodyLength:-1,env:{FormData:De.classes.FormData,Blob:De.classes.Blob},validateStatus:function(e){return e>=200&&e<300},headers:{common:{Accept:"application/json, text/plain, */*","Content-Type":void 0}}};ye.forEach(["delete","get","head","post","put","patch"],(function(e){qe.headers[e]={};}));var Me=qe,ze=ye.toObjectSet(["age","authorization","content-length","content-type","etag","expires","from","host","if-modified-since","if-unmodified-since","last-modified","location","max-forwards","proxy-authorization","referer","retry-after","user-agent"]),He=Symbol("internals");function Je(e){return e&&String(e).trim().toLowerCase()}function We(e){return !1===e||null==e?e:ye.isArray(e)?e.map(We):String(e)}function Ge(e,t,r,n,o){return ye.isFunction(n)?n.call(this,t,r):(o&&(t=r),ye.isString(t)?ye.isString(n)?-1!==t.indexOf(n):ye.isRegExp(n)?n.test(t):void 0:void 0)}var Ke=function(e,t){function r(e){d(this,r),e&&this.set(e);}return y(r,[{key:"set",value:function(e,t,r){var n=this;function o(e,t,r){var o=Je(t);if(!o)throw new Error("header name must be a non-empty string");var i=ye.findKey(n,o);(!i||void 0===n[i]||!0===r||void 0===r&&!1!==n[i])&&(n[i||t]=We(e));}var i=function(e,t){return ye.forEach(e,(function(e,r){return o(e,r,t)}))};if(ye.isPlainObject(e)||e instanceof this.constructor)i(e,t);else if(ye.isString(e)&&(e=e.trim())&&!/^[-_a-zA-Z0-9^`|~,!#$%&'*+.]+$/.test(e.trim()))i(function(e){var t,r,n,o={};return e&&e.split("\n").forEach((function(e){n=e.indexOf(":"),t=e.substring(0,n).trim().toLowerCase(),r=e.substring(n+1).trim(),!t||o[t]&&ze[t]||("set-cookie"===t?o[t]?o[t].push(r):o[t]=[r]:o[t]=o[t]?o[t]+", "+r:r);})),o}(e),t);else if(ye.isHeaders(e)){var a,u=function(e,t){var r="undefined"!=typeof Symbol&&e[Symbol.iterator]||e["@@iterator"];if(!r){if(Array.isArray(e)||(r=O(e))||t&&e&&"number"==typeof e.length){r&&(e=r);var n=0,o=function(){};return {s:o,n:function(){return n>=e.length?{done:!0}:{done:!1,value:e[n++]}},e:function(e){throw e},f:o}}throw new TypeError("Invalid attempt to iterate non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method.")}var i,a=!0,u=!1;return {s:function(){r=r.call(e);},n:function(){var e=r.next();return a=e.done,e},e:function(e){u=!0,i=e;},f:function(){try{a||null==r.return||r.return();}finally{if(u)throw i}}}}(e.entries());try{for(u.s();!(a=u.n()).done;){var s=b(a.value,2),c=s[0];o(s[1],c,r);}}catch(e){u.e(e);}finally{u.f();}}else null!=e&&o(t,e,r);return this}},{key:"get",value:function(e,t){if(e=Je(e)){var r=ye.findKey(this,e);if(r){var n=this[r];if(!t)return n;if(!0===t)return function(e){for(var t,r=Object.create(null),n=/([^\s,;=]+)\s*(?:=\s*([^,;]+))?/g;t=n.exec(e);)r[t[1]]=t[2];return r}(n);if(ye.isFunction(t))return t.call(this,n,r);if(ye.isRegExp(t))return t.exec(n);throw new TypeError("parser must be boolean|regexp|function")}}}},{key:"has",value:function(e,t){if(e=Je(e)){var r=ye.findKey(this,e);return !(!r||void 0===this[r]||t&&!Ge(0,this[r],r,t))}return !1}},{key:"delete",value:function(e,t){var r=this,n=!1;function o(e){if(e=Je(e)){var o=ye.findKey(r,e);!o||t&&!Ge(0,r[o],o,t)||(delete r[o],n=!0);}}return ye.isArray(e)?e.forEach(o):o(e),n}},{key:"clear",value:function(e){for(var t=Object.keys(this),r=t.length,n=!1;r--;){var o=t[r];e&&!Ge(0,this[o],o,e,!0)||(delete this[o],n=!0);}return n}},{key:"normalize",value:function(e){var t=this,r={};return ye.forEach(this,(function(n,o){var i=ye.findKey(r,o);if(i)return t[i]=We(n),void delete t[o];var a=e?function(e){return e.trim().toLowerCase().replace(/([a-z\d])(\w*)/g,(function(e,t,r){return t.toUpperCase()+r}))}(o):String(o).trim();a!==o&&delete t[o],t[a]=We(n),r[a]=!0;})),this}},{key:"concat",value:function(){for(var e,t=arguments.length,r=new Array(t),n=0;n<t;n++)r[n]=arguments[n];return (e=this.constructor).concat.apply(e,[this].concat(r))}},{key:"toJSON",value:function(e){var t=Object.create(null);return ye.forEach(this,(function(r,n){null!=r&&!1!==r&&(t[n]=e&&ye.isArray(r)?r.join(", "):r);})),t}},{key:Symbol.iterator,value:function(){return Object.entries(this.toJSON())[Symbol.iterator]()}},{key:"toString",value:function(){return Object.entries(this.toJSON()).map((function(e){var t=b(e,2);return t[0]+": "+t[1]})).join("\n")}},{key:Symbol.toStringTag,get:function(){return "AxiosHeaders"}}],[{key:"from",value:function(e){return e instanceof this?e:new this(e)}},{key:"concat",value:function(e){for(var t=new this(e),r=arguments.length,n=new Array(r>1?r-1:0),o=1;o<r;o++)n[o-1]=arguments[o];return n.forEach((function(e){return t.set(e)})),t}},{key:"accessor",value:function(e){var t=(this[He]=this[He]={accessors:{}}).accessors,r=this.prototype;function n(e){var n=Je(e);t[n]||(!function(e,t){var r=ye.toCamelCase(" "+t);["get","set","has"].forEach((function(n){Object.defineProperty(e,n+r,{value:function(e,r,o){return this[n].call(this,t,e,r,o)},configurable:!0});}));}(r,e),t[n]=!0);}return ye.isArray(e)?e.forEach(n):n(e),this}}]),r}();Ke.accessor(["Content-Type","Content-Length","Accept","Accept-Encoding","User-Agent","Authorization"]),ye.reduceDescriptors(Ke.prototype,(function(e,t){var r=e.value,n=t[0].toUpperCase()+t.slice(1);return {get:function(){return r},set:function(e){this[n]=e;}}})),ye.freezeMethods(Ke);var Ve=Ke;function Xe(e,t){var r=this||Me,n=t||r,o=Ve.from(n.headers),i=n.data;return ye.forEach(e,(function(e){i=e.call(r,i,o.normalize(),t?t.status:void 0);})),o.normalize(),i}function $e(e){return !(!e||!e.__CANCEL__)}function Ye(e,t,r){me.call(this,null==e?"canceled":e,me.ERR_CANCELED,t,r),this.name="CanceledError";}function Qe(e,t,r){var n=r.config.validateStatus;r.status&&n&&!n(r.status)?t(new me("Request failed with status code "+r.status,[me.ERR_BAD_REQUEST,me.ERR_BAD_RESPONSE][Math.floor(r.status/100)-4],r.config,r.request,r)):e(r);}function Ze(e,t){e=e||10;var r,n=new Array(e),o=new Array(e),i=0,a=0;return t=void 0!==t?t:1e3,function(u){var s=Date.now(),c=o[a];r||(r=s),n[i]=u,o[i]=s;for(var f=a,l=0;f!==i;)l+=n[f++],f%=e;if((i=(i+1)%e)===a&&(a=(a+1)%e),!(s-r<t)){var p=c&&s-c;return p?Math.round(1e3*l/p):void 0}}}function et(e,t){var r,n,o=0,i=1e3/t,a=function(t){var i=arguments.length>1&&void 0!==arguments[1]?arguments[1]:Date.now();o=i,r=null,n&&(clearTimeout(n),n=null),e.apply(null,t);};return [function(){for(var e=Date.now(),t=e-o,u=arguments.length,s=new Array(u),c=0;c<u;c++)s[c]=arguments[c];t>=i?a(s,e):(r=s,n||(n=setTimeout((function(){n=null,a(r);}),i-t)));},function(){return r&&a(r)}]}ye.inherits(Ye,me,{__CANCEL__:!0});var tt=function(e,t){var r=arguments.length>2&&void 0!==arguments[2]?arguments[2]:3,n=0,o=Ze(50,250);return et((function(r){var i=r.loaded,a=r.lengthComputable?r.total:void 0,u=i-n,s=o(u);n=i;var c=m({loaded:i,total:a,progress:a?i/a:void 0,bytes:u,rate:s||void 0,estimated:s&&a&&i<=a?(a-i)/s:void 0,event:r,lengthComputable:null!=a},t?"download":"upload",!0);e(c);}),r)},rt=function(e,t){var r=null!=e;return [function(n){return t[0]({lengthComputable:r,total:e,loaded:n})},t[1]]},nt=function(e){return function(){for(var t=arguments.length,r=new Array(t),n=0;n<t;n++)r[n]=arguments[n];return ye.asap((function(){return e.apply(void 0,r)}))}},ot=De.hasStandardBrowserEnv?function(e,t){return function(r){return r=new URL(r,De.origin),e.protocol===r.protocol&&e.host===r.host&&(t||e.port===r.port)}}(new URL(De.origin),De.navigator&&/(msie|trident)/i.test(De.navigator.userAgent)):function(){return !0},it=De.hasStandardBrowserEnv?{write:function(e,t,r,n,o,i){var a=[e+"="+encodeURIComponent(t)];ye.isNumber(r)&&a.push("expires="+new Date(r).toGMTString()),ye.isString(n)&&a.push("path="+n),ye.isString(o)&&a.push("domain="+o),!0===i&&a.push("secure"),document.cookie=a.join("; ");},read:function(e){var t=document.cookie.match(new RegExp("(^|;\\s*)("+e+")=([^;]*)"));return t?decodeURIComponent(t[3]):null},remove:function(e){this.write(e,"",Date.now()-864e5);}}:{write:function(){},read:function(){return null},remove:function(){}};function at(e,t){return e&&!/^([a-z][a-z\d+\-.]*:)?\/\//i.test(t)?function(e,t){return t?e.replace(/\/?\/$/,"")+"/"+t.replace(/^\/+/,""):e}(e,t):t}var ut=function(e){return e instanceof Ve?u({},e):e};function st(e,t){t=t||{};var r={};function n(e,t,r,n){return ye.isPlainObject(e)&&ye.isPlainObject(t)?ye.merge.call({caseless:n},e,t):ye.isPlainObject(t)?ye.merge({},t):ye.isArray(t)?t.slice():t}function o(e,t,r,o){return ye.isUndefined(t)?ye.isUndefined(e)?void 0:n(void 0,e,0,o):n(e,t,0,o)}function i(e,t){if(!ye.isUndefined(t))return n(void 0,t)}function a(e,t){return ye.isUndefined(t)?ye.isUndefined(e)?void 0:n(void 0,e):n(void 0,t)}function u(r,o,i){return i in t?n(r,o):i in e?n(void 0,r):void 0}var s={url:i,method:i,data:i,baseURL:a,transformRequest:a,transformResponse:a,paramsSerializer:a,timeout:a,timeoutMessage:a,withCredentials:a,withXSRFToken:a,adapter:a,responseType:a,xsrfCookieName:a,xsrfHeaderName:a,onUploadProgress:a,onDownloadProgress:a,decompress:a,maxContentLength:a,maxBodyLength:a,beforeRedirect:a,transport:a,httpAgent:a,httpsAgent:a,cancelToken:a,socketPath:a,responseEncoding:a,validateStatus:u,headers:function(e,t,r){return o(ut(e),ut(t),0,!0)}};return ye.forEach(Object.keys(Object.assign({},e,t)),(function(n){var i=s[n]||o,a=i(e[n],t[n],n);ye.isUndefined(a)&&i!==u||(r[n]=a);})),r}var ct,ft,lt=function(e){var t,r,n=st({},e),o=n.data,i=n.withXSRFToken,a=n.xsrfHeaderName,u=n.xsrfCookieName,s=n.headers,c=n.auth;if(n.headers=s=Ve.from(s),n.url=Ae(at(n.baseURL,n.url),e.params,e.paramsSerializer),c&&s.set("Authorization","Basic "+btoa((c.username||"")+":"+(c.password?unescape(encodeURIComponent(c.password)):""))),ye.isFormData(o))if(De.hasStandardBrowserEnv||De.hasStandardBrowserWebWorkerEnv)s.setContentType(void 0);else if(!1!==(t=s.getContentType())){var f=t?t.split(";").map((function(e){return e.trim()})).filter(Boolean):[],l=w(r=f)||E(r)||O(r)||x(),p=l[0],h=l.slice(1);s.setContentType([p||"multipart/form-data"].concat(g(h)).join("; "));}if(De.hasStandardBrowserEnv&&(i&&ye.isFunction(i)&&(i=i(n)),i||!1!==i&&ot(n.url))){var d=a&&u&&it.read(u);d&&s.set(a,d);}return n},pt="undefined"!=typeof XMLHttpRequest&&function(e){return new Promise((function(t,r){var n,o,i,a,u,s=lt(e),c=s.data,f=Ve.from(s.headers).normalize(),l=s.responseType,p=s.onUploadProgress,h=s.onDownloadProgress;function d(){a&&a(),u&&u(),s.cancelToken&&s.cancelToken.unsubscribe(n),s.signal&&s.signal.removeEventListener("abort",n);}var v=new XMLHttpRequest;function y(){if(v){var n=Ve.from("getAllResponseHeaders"in v&&v.getAllResponseHeaders());Qe((function(e){t(e),d();}),(function(e){r(e),d();}),{data:l&&"text"!==l&&"json"!==l?v.response:v.responseText,status:v.status,statusText:v.statusText,headers:n,config:e,request:v}),v=null;}}if(v.open(s.method.toUpperCase(),s.url,!0),v.timeout=s.timeout,"onloadend"in v?v.onloadend=y:v.onreadystatechange=function(){v&&4===v.readyState&&(0!==v.status||v.responseURL&&0===v.responseURL.indexOf("file:"))&&setTimeout(y);},v.onabort=function(){v&&(r(new me("Request aborted",me.ECONNABORTED,e,v)),v=null);},v.onerror=function(){r(new me("Network Error",me.ERR_NETWORK,e,v)),v=null;},v.ontimeout=function(){var t=s.timeout?"timeout of "+s.timeout+"ms exceeded":"timeout exceeded",n=s.transitional||Le;s.timeoutErrorMessage&&(t=s.timeoutErrorMessage),r(new me(t,n.clarifyTimeoutError?me.ETIMEDOUT:me.ECONNABORTED,e,v)),v=null;},void 0===c&&f.setContentType(null),"setRequestHeader"in v&&ye.forEach(f.toJSON(),(function(e,t){v.setRequestHeader(t,e);})),ye.isUndefined(s.withCredentials)||(v.withCredentials=!!s.withCredentials),l&&"json"!==l&&(v.responseType=s.responseType),h){var m=b(tt(h,!0),2);i=m[0],u=m[1],v.addEventListener("progress",i);}if(p&&v.upload){var g=b(tt(p),2);o=g[0],a=g[1],v.upload.addEventListener("progress",o),v.upload.addEventListener("loadend",a);}(s.cancelToken||s.signal)&&(n=function(t){v&&(r(!t||t.type?new Ye(null,e,v):t),v.abort(),v=null);},s.cancelToken&&s.cancelToken.subscribe(n),s.signal&&(s.signal.aborted?n():s.signal.addEventListener("abort",n)));var w,E,O=(w=s.url,(E=/^([-+\w]{1,25})(:?\/\/|:)/.exec(w))&&E[1]||"");O&&-1===De.protocols.indexOf(O)?r(new me("Unsupported protocol "+O+":",me.ERR_BAD_REQUEST,e)):v.send(c||null);}))},ht=function(e,t){var r=(e=e?e.filter(Boolean):[]).length;if(t||r){var n,o=new AbortController,i=function(e){if(!n){n=!0,u();var t=e instanceof Error?e:this.reason;o.abort(t instanceof me?t:new Ye(t instanceof Error?t.message:t));}},a=t&&setTimeout((function(){a=null,i(new me("timeout ".concat(t," of ms exceeded"),me.ETIMEDOUT));}),t),u=function(){e&&(a&&clearTimeout(a),a=null,e.forEach((function(e){e.unsubscribe?e.unsubscribe(i):e.removeEventListener("abort",i);})),e=null);};e.forEach((function(e){return e.addEventListener("abort",i)}));var s=o.signal;return s.unsubscribe=function(){return ye.asap(u)},s}},dt=s().mark((function e(t,r){var n,o,i;return s().wrap((function(e){for(;;)switch(e.prev=e.next){case 0:if(n=t.byteLength,r&&!(n<r)){e.next=5;break}return e.next=4,t;case 4:return e.abrupt("return");case 5:o=0;case 6:if(!(o<n)){e.next=13;break}return i=o+r,e.next=10,t.slice(o,i);case 10:o=i,e.next=6;break;case 13:case"end":return e.stop()}}),e)})),vt=function(){var e=l(s().mark((function e(t,o){var a,u,c,f,l,p;return s().wrap((function(e){for(;;)switch(e.prev=e.next){case 0:a=!1,u=!1,e.prev=2,f=n(yt(t));case 4:return e.next=6,i(f.next());case 6:if(!(a=!(l=e.sent).done)){e.next=12;break}return p=l.value,e.delegateYield(r(n(dt(p,o))),"t0",9);case 9:a=!1,e.next=4;break;case 12:e.next=18;break;case 14:e.prev=14,e.t1=e.catch(2),u=!0,c=e.t1;case 18:if(e.prev=18,e.prev=19,!a||null==f.return){e.next=23;break}return e.next=23,i(f.return());case 23:if(e.prev=23,!u){e.next=26;break}throw c;case 26:return e.finish(23);case 27:return e.finish(18);case 28:case"end":return e.stop()}}),e,null,[[2,14,18,28],[19,,23,27]])})));return function(t,r){return e.apply(this,arguments)}}(),yt=function(){var e=l(s().mark((function e(t){var o,a,u,c;return s().wrap((function(e){for(;;)switch(e.prev=e.next){case 0:if(!t[Symbol.asyncIterator]){e.next=3;break}return e.delegateYield(r(n(t)),"t0",2);case 2:return e.abrupt("return");case 3:o=t.getReader(),e.prev=4;case 5:return e.next=7,i(o.read());case 7:if(a=e.sent,u=a.done,c=a.value,!u){e.next=12;break}return e.abrupt("break",16);case 12:return e.next=14,c;case 14:e.next=5;break;case 16:return e.prev=16,e.next=19,i(o.cancel());case 19:return e.finish(16);case 20:case"end":return e.stop()}}),e,null,[[4,,16,20]])})));return function(t){return e.apply(this,arguments)}}(),mt=function(e,t,r,n){var o,i=vt(e,t),a=0,u=function(e){o||(o=!0,n&&n(e));};return new ReadableStream({pull:function(e){return h(s().mark((function t(){var n,o,c,f,l;return s().wrap((function(t){for(;;)switch(t.prev=t.next){case 0:return t.prev=0,t.next=3,i.next();case 3:if(n=t.sent,o=n.done,c=n.value,!o){t.next=10;break}return u(),e.close(),t.abrupt("return");case 10:f=c.byteLength,r&&(l=a+=f,r(l)),e.enqueue(new Uint8Array(c)),t.next=19;break;case 15:throw t.prev=15,t.t0=t.catch(0),u(t.t0),t.t0;case 19:case"end":return t.stop()}}),t,null,[[0,15]])})))()},cancel:function(e){return u(e),i.return()}},{highWaterMark:2})},bt="function"==typeof fetch&&"function"==typeof Request&&"function"==typeof Response,gt=bt&&"function"==typeof ReadableStream,wt=bt&&("function"==typeof TextEncoder?(ct=new TextEncoder,function(e){return ct.encode(e)}):function(){var e=h(s().mark((function e(t){return s().wrap((function(e){for(;;)switch(e.prev=e.next){case 0:return e.t0=Uint8Array,e.next=3,new Response(t).arrayBuffer();case 3:return e.t1=e.sent,e.abrupt("return",new e.t0(e.t1));case 5:case"end":return e.stop()}}),e)})));return function(t){return e.apply(this,arguments)}}()),Et=function(e){try{for(var t=arguments.length,r=new Array(t>1?t-1:0),n=1;n<t;n++)r[n-1]=arguments[n];return !!e.apply(void 0,r)}catch(e){return !1}},Ot=gt&&Et((function(){var e=!1,t=new Request(De.origin,{body:new ReadableStream,method:"POST",get duplex(){return e=!0,"half"}}).headers.has("Content-Type");return e&&!t})),St=gt&&Et((function(){return ye.isReadableStream(new Response("").body)})),xt={stream:St&&function(e){return e.body}};bt&&(ft=new Response,["text","arrayBuffer","blob","formData","stream"].forEach((function(e){!xt[e]&&(xt[e]=ye.isFunction(ft[e])?function(t){return t[e]()}:function(t,r){throw new me("Response type '".concat(e,"' is not supported"),me.ERR_NOT_SUPPORT,r)});})));var Rt=function(){var e=h(s().mark((function e(t){var r;return s().wrap((function(e){for(;;)switch(e.prev=e.next){case 0:if(null!=t){e.next=2;break}return e.abrupt("return",0);case 2:if(!ye.isBlob(t)){e.next=4;break}return e.abrupt("return",t.size);case 4:if(!ye.isSpecCompliantForm(t)){e.next=9;break}return r=new Request(De.origin,{method:"POST",body:t}),e.next=8,r.arrayBuffer();case 8:case 15:return e.abrupt("return",e.sent.byteLength);case 9:if(!ye.isArrayBufferView(t)&&!ye.isArrayBuffer(t)){e.next=11;break}return e.abrupt("return",t.byteLength);case 11:if(ye.isURLSearchParams(t)&&(t+=""),!ye.isString(t)){e.next=16;break}return e.next=15,wt(t);case 16:case"end":return e.stop()}}),e)})));return function(t){return e.apply(this,arguments)}}(),Tt=function(){var e=h(s().mark((function e(t,r){var n;return s().wrap((function(e){for(;;)switch(e.prev=e.next){case 0:return n=ye.toFiniteNumber(t.getContentLength()),e.abrupt("return",null==n?Rt(r):n);case 2:case"end":return e.stop()}}),e)})));return function(t,r){return e.apply(this,arguments)}}(),kt=bt&&function(){var e=h(s().mark((function e(t){var r,n,o,i,a,c,f,l,p,h,d,v,y,m,g,w,E,O,S,x,R,T,k,j,A,P,L,N,_,C,F,U,B,D;return s().wrap((function(e){for(;;)switch(e.prev=e.next){case 0:if(r=lt(t),n=r.url,o=r.method,i=r.data,a=r.signal,c=r.cancelToken,f=r.timeout,l=r.onDownloadProgress,p=r.onUploadProgress,h=r.responseType,d=r.headers,v=r.withCredentials,y=void 0===v?"same-origin":v,m=r.fetchOptions,h=h?(h+"").toLowerCase():"text",g=ht([a,c&&c.toAbortSignal()],f),E=g&&g.unsubscribe&&function(){g.unsubscribe();},e.prev=4,e.t0=p&&Ot&&"get"!==o&&"head"!==o,!e.t0){e.next=11;break}return e.next=9,Tt(d,i);case 9:e.t1=O=e.sent,e.t0=0!==e.t1;case 11:if(!e.t0){e.next=15;break}S=new Request(n,{method:"POST",body:i,duplex:"half"}),ye.isFormData(i)&&(x=S.headers.get("content-type"))&&d.setContentType(x),S.body&&(R=rt(O,tt(nt(p))),T=b(R,2),k=T[0],j=T[1],i=mt(S.body,65536,k,j));case 15:return ye.isString(y)||(y=y?"include":"omit"),A="credentials"in Request.prototype,w=new Request(n,u(u({},m),{},{signal:g,method:o.toUpperCase(),headers:d.normalize().toJSON(),body:i,duplex:"half",credentials:A?y:void 0})),e.next=20,fetch(w);case 20:return P=e.sent,L=St&&("stream"===h||"response"===h),St&&(l||L&&E)&&(N={},["status","statusText","headers"].forEach((function(e){N[e]=P[e];})),_=ye.toFiniteNumber(P.headers.get("content-length")),C=l&&rt(_,tt(nt(l),!0))||[],F=b(C,2),U=F[0],B=F[1],P=new Response(mt(P.body,65536,U,(function(){B&&B(),E&&E();})),N)),h=h||"text",e.next=26,xt[ye.findKey(xt,h)||"text"](P,t);case 26:return D=e.sent,!L&&E&&E(),e.next=30,new Promise((function(e,r){Qe(e,r,{data:D,headers:Ve.from(P.headers),status:P.status,statusText:P.statusText,config:t,request:w});}));case 30:return e.abrupt("return",e.sent);case 33:if(e.prev=33,e.t2=e.catch(4),E&&E(),!e.t2||"TypeError"!==e.t2.name||!/fetch/i.test(e.t2.message)){e.next=38;break}throw Object.assign(new me("Network Error",me.ERR_NETWORK,t,w),{cause:e.t2.cause||e.t2});case 38:throw me.from(e.t2,e.t2&&e.t2.code,t,w);case 39:case"end":return e.stop()}}),e,null,[[4,33]])})));return function(t){return e.apply(this,arguments)}}(),jt={http:null,xhr:pt,fetch:kt};ye.forEach(jt,(function(e,t){if(e){try{Object.defineProperty(e,"name",{value:t});}catch(e){}Object.defineProperty(e,"adapterName",{value:t});}}));var At=function(e){return "- ".concat(e)},Pt=function(e){return ye.isFunction(e)||null===e||!1===e},Lt=function(e){for(var t,r,n=(e=ye.isArray(e)?e:[e]).length,o={},i=0;i<n;i++){var a=void 0;if(r=t=e[i],!Pt(t)&&void 0===(r=jt[(a=String(t)).toLowerCase()]))throw new me("Unknown adapter '".concat(a,"'"));if(r)break;o[a||"#"+i]=r;}if(!r){var u=Object.entries(o).map((function(e){var t=b(e,2),r=t[0],n=t[1];return "adapter ".concat(r," ")+(!1===n?"is not supported by the environment":"is not available in the build")}));throw new me("There is no suitable adapter to dispatch the request "+(n?u.length>1?"since :\n"+u.map(At).join("\n"):" "+At(u[0]):"as no adapter specified"),"ERR_NOT_SUPPORT")}return r};function Nt(e){if(e.cancelToken&&e.cancelToken.throwIfRequested(),e.signal&&e.signal.aborted)throw new Ye(null,e)}function _t(e){return Nt(e),e.headers=Ve.from(e.headers),e.data=Xe.call(e,e.transformRequest),-1!==["post","put","patch"].indexOf(e.method)&&e.headers.setContentType("application/x-www-form-urlencoded",!1),Lt(e.adapter||Me.adapter)(e).then((function(t){return Nt(e),t.data=Xe.call(e,e.transformResponse,t),t.headers=Ve.from(t.headers),t}),(function(t){return $e(t)||(Nt(e),t&&t.response&&(t.response.data=Xe.call(e,e.transformResponse,t.response),t.response.headers=Ve.from(t.response.headers))),Promise.reject(t)}))}var Ct="1.7.9",Ft={};["object","boolean","number","function","string","symbol"].forEach((function(e,t){Ft[e]=function(r){return f(r)===e||"a"+(t<1?"n ":" ")+e};}));var Ut={};Ft.transitional=function(e,t,r){function n(e,t){return "[Axios v1.7.9] Transitional option '"+e+"'"+t+(r?". "+r:"")}return function(r,o,i){if(!1===e)throw new me(n(o," has been removed"+(t?" in "+t:"")),me.ERR_DEPRECATED);return t&&!Ut[o]&&(Ut[o]=!0,console.warn(n(o," has been deprecated since v"+t+" and will be removed in the near future"))),!e||e(r,o,i)}},Ft.spelling=function(e){return function(t,r){return console.warn("".concat(r," is likely a misspelling of ").concat(e)),!0}};var Bt={assertOptions:function(e,t,r){if("object"!==f(e))throw new me("options must be an object",me.ERR_BAD_OPTION_VALUE);for(var n=Object.keys(e),o=n.length;o-- >0;){var i=n[o],a=t[i];if(a){var u=e[i],s=void 0===u||a(u,i,e);if(!0!==s)throw new me("option "+i+" must be "+s,me.ERR_BAD_OPTION_VALUE)}else if(!0!==r)throw new me("Unknown option "+i,me.ERR_BAD_OPTION)}},validators:Ft},Dt=Bt.validators,It=function(){function e(t){d(this,e),this.defaults=t,this.interceptors={request:new Pe,response:new Pe};}var t;return y(e,[{key:"request",value:(t=h(s().mark((function e(t,r){var n,o;return s().wrap((function(e){for(;;)switch(e.prev=e.next){case 0:return e.prev=0,e.next=3,this._request(t,r);case 3:return e.abrupt("return",e.sent);case 6:if(e.prev=6,e.t0=e.catch(0),e.t0 instanceof Error){n={},Error.captureStackTrace?Error.captureStackTrace(n):n=new Error,o=n.stack?n.stack.replace(/^.+\n/,""):"";try{e.t0.stack?o&&!String(e.t0.stack).endsWith(o.replace(/^.+\n.+\n/,""))&&(e.t0.stack+="\n"+o):e.t0.stack=o;}catch(e){}}throw e.t0;case 10:case"end":return e.stop()}}),e,this,[[0,6]])}))),function(e,r){return t.apply(this,arguments)})},{key:"_request",value:function(e,t){"string"==typeof e?(t=t||{}).url=e:t=e||{};var r=t=st(this.defaults,t),n=r.transitional,o=r.paramsSerializer,i=r.headers;void 0!==n&&Bt.assertOptions(n,{silentJSONParsing:Dt.transitional(Dt.boolean),forcedJSONParsing:Dt.transitional(Dt.boolean),clarifyTimeoutError:Dt.transitional(Dt.boolean)},!1),null!=o&&(ye.isFunction(o)?t.paramsSerializer={serialize:o}:Bt.assertOptions(o,{encode:Dt.function,serialize:Dt.function},!0)),Bt.assertOptions(t,{baseUrl:Dt.spelling("baseURL"),withXsrfToken:Dt.spelling("withXSRFToken")},!0),t.method=(t.method||this.defaults.method||"get").toLowerCase();var a=i&&ye.merge(i.common,i[t.method]);i&&ye.forEach(["delete","get","head","post","put","patch","common"],(function(e){delete i[e];})),t.headers=Ve.concat(a,i);var u=[],s=!0;this.interceptors.request.forEach((function(e){"function"==typeof e.runWhen&&!1===e.runWhen(t)||(s=s&&e.synchronous,u.unshift(e.fulfilled,e.rejected));}));var c,f=[];this.interceptors.response.forEach((function(e){f.push(e.fulfilled,e.rejected);}));var l,p=0;if(!s){var h=[_t.bind(this),void 0];for(h.unshift.apply(h,u),h.push.apply(h,f),l=h.length,c=Promise.resolve(t);p<l;)c=c.then(h[p++],h[p++]);return c}l=u.length;var d=t;for(p=0;p<l;){var v=u[p++],y=u[p++];try{d=v(d);}catch(e){y.call(this,e);break}}try{c=_t.call(this,d);}catch(e){return Promise.reject(e)}for(p=0,l=f.length;p<l;)c=c.then(f[p++],f[p++]);return c}},{key:"getUri",value:function(e){return Ae(at((e=st(this.defaults,e)).baseURL,e.url),e.params,e.paramsSerializer)}}]),e}();ye.forEach(["delete","get","head","options"],(function(e){It.prototype[e]=function(t,r){return this.request(st(r||{},{method:e,url:t,data:(r||{}).data}))};})),ye.forEach(["post","put","patch"],(function(e){function t(t){return function(r,n,o){return this.request(st(o||{},{method:e,headers:t?{"Content-Type":"multipart/form-data"}:{},url:r,data:n}))}}It.prototype[e]=t(),It.prototype[e+"Form"]=t(!0);}));var qt=It,Mt=function(){function e(t){if(d(this,e),"function"!=typeof t)throw new TypeError("executor must be a function.");var r;this.promise=new Promise((function(e){r=e;}));var n=this;this.promise.then((function(e){if(n._listeners){for(var t=n._listeners.length;t-- >0;)n._listeners[t](e);n._listeners=null;}})),this.promise.then=function(e){var t,r=new Promise((function(e){n.subscribe(e),t=e;})).then(e);return r.cancel=function(){n.unsubscribe(t);},r},t((function(e,t,o){n.reason||(n.reason=new Ye(e,t,o),r(n.reason));}));}return y(e,[{key:"throwIfRequested",value:function(){if(this.reason)throw this.reason}},{key:"subscribe",value:function(e){this.reason?e(this.reason):this._listeners?this._listeners.push(e):this._listeners=[e];}},{key:"unsubscribe",value:function(e){if(this._listeners){var t=this._listeners.indexOf(e);-1!==t&&this._listeners.splice(t,1);}}},{key:"toAbortSignal",value:function(){var e=this,t=new AbortController,r=function(e){t.abort(e);};return this.subscribe(r),t.signal.unsubscribe=function(){return e.unsubscribe(r)},t.signal}}],[{key:"source",value:function(){var t;return {token:new e((function(e){t=e;})),cancel:t}}}]),e}(),zt=Mt;var Ht={Continue:100,SwitchingProtocols:101,Processing:102,EarlyHints:103,Ok:200,Created:201,Accepted:202,NonAuthoritativeInformation:203,NoContent:204,ResetContent:205,PartialContent:206,MultiStatus:207,AlreadyReported:208,ImUsed:226,MultipleChoices:300,MovedPermanently:301,Found:302,SeeOther:303,NotModified:304,UseProxy:305,Unused:306,TemporaryRedirect:307,PermanentRedirect:308,BadRequest:400,Unauthorized:401,PaymentRequired:402,Forbidden:403,NotFound:404,MethodNotAllowed:405,NotAcceptable:406,ProxyAuthenticationRequired:407,RequestTimeout:408,Conflict:409,Gone:410,LengthRequired:411,PreconditionFailed:412,PayloadTooLarge:413,UriTooLong:414,UnsupportedMediaType:415,RangeNotSatisfiable:416,ExpectationFailed:417,ImATeapot:418,MisdirectedRequest:421,UnprocessableEntity:422,Locked:423,FailedDependency:424,TooEarly:425,UpgradeRequired:426,PreconditionRequired:428,TooManyRequests:429,RequestHeaderFieldsTooLarge:431,UnavailableForLegalReasons:451,InternalServerError:500,NotImplemented:501,BadGateway:502,ServiceUnavailable:503,GatewayTimeout:504,HttpVersionNotSupported:505,VariantAlsoNegotiates:506,InsufficientStorage:507,LoopDetected:508,NotExtended:510,NetworkAuthenticationRequired:511};Object.entries(Ht).forEach((function(e){var t=b(e,2),r=t[0],n=t[1];Ht[n]=r;}));var Jt=Ht;var Wt=function e(t){var r=new qt(t),n=R(qt.prototype.request,r);return ye.extend(n,qt.prototype,r,{allOwnKeys:!0}),ye.extend(n,r,null,{allOwnKeys:!0}),n.create=function(r){return e(st(t,r))},n}(Me);return Wt.Axios=qt,Wt.CanceledError=Ye,Wt.CancelToken=zt,Wt.isCancel=$e,Wt.VERSION=Ct,Wt.toFormData=xe,Wt.AxiosError=me,Wt.Cancel=Wt.CanceledError,Wt.all=function(e){return Promise.all(e)},Wt.spread=function(e){return function(t){return e.apply(null,t)}},Wt.isAxiosError=function(e){return ye.isObject(e)&&!0===e.isAxiosError},Wt.mergeConfig=st,Wt.AxiosHeaders=Ve,Wt.formToJSON=function(e){return Ie(ye.isHTMLForm(e)?new FormData(e):e)},Wt.getAdapter=Lt,Wt.HttpStatusCode=Jt,Wt.default=Wt,Wt}));

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
      // Allow provider without '@': "provider:prefix:name"
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
  return !!// Check prefix: cannot be empty, unless allowSimpleName is enabled
  // Check name: cannot be empty
  ((allowSimpleName && icon.prefix === "" || !!icon.prefix) && !!icon.name);
};

const defaultIconDimensions = Object.freeze(
  {
    left: 0,
    top: 0,
    width: 16,
    height: 16
  }
);
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
  (Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}

function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(
      icons[name2] || aliases[name2],
      currentProps
    );
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
    if (
      // Name cannot be empty
      !name || // Must have body
      typeof icon.body !== "string" || // Check other props
      !checkOptionalProps(
        icon,
        defaultExtendedIconProps
      )
    ) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (
      // Name cannot be empty
      !name || // Parent must be set and point to existing icon
      typeof parent !== "string" || !icons[parent] && !aliases[parent] || // Check other props
      !checkOptionalProps(
        icon,
        defaultExtendedIconProps
      )
    ) {
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
function addIconSet(storage, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage.icons[name] = icon;
    } else {
      storage.missing.add(name);
    }
  });
}
function addIconToStorage(storage, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage.icons[name] = { ...icon };
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
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage = getStorage(icon.provider, icon.prefix);
  if (data) {
    return addIconToStorage(storage, icon.name, data);
  } else {
    storage.missing.add(icon.name);
    return true;
  }
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
        if (addIcon(name, icon)) {
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
  const storage = getStorage(provider, prefix);
  return !!addIconSet(storage, data);
}

const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  // Dimensions
  ...defaultIconSizeCustomisations,
  // Transformations
  ...defaultIconTransformations
});
"IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);

const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
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
    // API hosts
    resources,
    // Root path
    path: source.path || "/",
    // URL length limit
    maxURL: source.maxURL || 500,
    // Timeout before next host is used.
    rotate: source.rotate || 750,
    // Timeout before failing query.
    timeout: source.timeout || 5e3,
    // Randomise default API end point.
    random: source.random === true,
    // Start index
    index: source.index || 0,
    // Receive data after time out (used if time out kicks in first, then API module sends data anyway).
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

({
    ...defaultIconCustomisations,
    inline: false,
});
const monotoneProps = {
    'background-color': 'currentColor',
};
const coloredProps = {
    'background-color': 'transparent',
};
// Dynamically add common props to variables above
const propsToAdd = {
    image: 'var(--svg)',
    repeat: 'no-repeat',
    size: '100% 100%',
};
const propsToAddTo = {
    '-webkit-mask': monotoneProps,
    'mask': monotoneProps,
    'background': coloredProps,
};
for (const prefix in propsToAddTo) {
    const list = propsToAddTo[prefix];
    for (const prop in propsToAdd) {
        list[prefix + '-' + prop] = propsToAdd[prop];
    }
}
/**
 * Initialise stuff
 */
// Enable short names
allowSimpleNames(true);
// Set API module
setAPIModule('', fetchAPIModule);
/**
 * Browser stuff
 */
if (typeof document !== 'undefined' && typeof window !== 'undefined') {
    const _window = window;
    // Load icons from global "IconifyPreload"
    if (_window.IconifyPreload !== void 0) {
        const preload = _window.IconifyPreload;
        const err = 'Invalid IconifyPreload syntax.';
        if (typeof preload === 'object' && preload !== null) {
            (preload instanceof Array ? preload : [preload]).forEach((item) => {
                try {
                    if (
                    // Check if item is an object and not null/array
                    typeof item !== 'object' ||
                        item === null ||
                        item instanceof Array ||
                        // Check for 'icons' and 'prefix'
                        typeof item.icons !== 'object' ||
                        typeof item.prefix !== 'string' ||
                        // Add icon set
                        !addCollection(item)) {
                        console.error(err);
                    }
                }
                catch (e) {
                    console.error(err);
                }
            });
        }
    }
    // Set API from global "IconifyProviders"
    if (_window.IconifyProviders !== void 0) {
        const providers = _window.IconifyProviders;
        if (typeof providers === 'object' && providers !== null) {
            for (let key in providers) {
                const err = 'IconifyProviders[' + key + '] is invalid.';
                try {
                    const value = providers[key];
                    if (typeof value !== 'object' ||
                        !value ||
                        value.resources === void 0) {
                        continue;
                    }
                    if (!addAPIProvider(key, value)) {
                        console.error(err);
                    }
                }
                catch (e) {
                    console.error(err);
                }
            }
        }
    }
}

/* generated by Svelte v3.59.1 */

function create_if_block_2(ctx) {
	let h2;
	let t;

	return {
		c() {
			h2 = element("h2");
			t = text(/*subheading*/ ctx[2]);
			this.h();
		},
		l(nodes) {
			h2 = claim_element(nodes, "H2", { class: true });
			var h2_nodes = children(h2);
			t = claim_text(h2_nodes, /*subheading*/ ctx[2]);
			h2_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h2, "class", "subheadline svelte-12dqoo3");
		},
		m(target, anchor) {
			insert_hydration(target, h2, anchor);
			append_hydration(h2, t);
		},
		p(ctx, dirty) {
			if (dirty & /*subheading*/ 4) set_data(t, /*subheading*/ ctx[2]);
		},
		d(detaching) {
			if (detaching) detach(h2);
		}
	};
}

// (202:2) {#if graphics.left}
function create_if_block_1(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { class: true, src: true, alt: true });
			this.h();
		},
		h() {
			attr(img, "class", "graphic left svelte-12dqoo3");
			if (!src_url_equal(img.src, img_src_value = /*graphics*/ ctx[1].left.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*graphics*/ ctx[1].left.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*graphics*/ 2 && !src_url_equal(img.src, img_src_value = /*graphics*/ ctx[1].left.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*graphics*/ 2 && img_alt_value !== (img_alt_value = /*graphics*/ ctx[1].left.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

// (205:2) {#if graphics.right}
function create_if_block(ctx) {
	let img;
	let img_src_value;
	let img_alt_value;

	return {
		c() {
			img = element("img");
			this.h();
		},
		l(nodes) {
			img = claim_element(nodes, "IMG", { class: true, src: true, alt: true });
			this.h();
		},
		h() {
			attr(img, "class", "graphic right svelte-12dqoo3");
			if (!src_url_equal(img.src, img_src_value = /*graphics*/ ctx[1].right.url)) attr(img, "src", img_src_value);
			attr(img, "alt", img_alt_value = /*graphics*/ ctx[1].right.alt);
		},
		m(target, anchor) {
			insert_hydration(target, img, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*graphics*/ 2 && !src_url_equal(img.src, img_src_value = /*graphics*/ ctx[1].right.url)) {
				attr(img, "src", img_src_value);
			}

			if (dirty & /*graphics*/ 2 && img_alt_value !== (img_alt_value = /*graphics*/ ctx[1].right.alt)) {
				attr(img, "alt", img_alt_value);
			}
		},
		d(detaching) {
			if (detaching) detach(img);
		}
	};
}

function create_fragment(ctx) {
	let section;
	let h1;
	let t0;
	let t1;
	let t2;
	let t3;
	let if_block0 = /*subheading*/ ctx[2] && create_if_block_2(ctx);
	let if_block1 = /*graphics*/ ctx[1].left && create_if_block_1(ctx);
	let if_block2 = /*graphics*/ ctx[1].right && create_if_block(ctx);

	return {
		c() {
			section = element("section");
			h1 = element("h1");
			t0 = text(/*heading*/ ctx[0]);
			t1 = space();
			if (if_block0) if_block0.c();
			t2 = space();
			if (if_block1) if_block1.c();
			t3 = space();
			if (if_block2) if_block2.c();
			this.h();
		},
		l(nodes) {
			section = claim_element(nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			h1 = claim_element(section_nodes, "H1", { class: true });
			var h1_nodes = children(h1);
			t0 = claim_text(h1_nodes, /*heading*/ ctx[0]);
			h1_nodes.forEach(detach);
			t1 = claim_space(section_nodes);
			if (if_block0) if_block0.l(section_nodes);
			t2 = claim_space(section_nodes);
			if (if_block1) if_block1.l(section_nodes);
			t3 = claim_space(section_nodes);
			if (if_block2) if_block2.l(section_nodes);
			section_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(h1, "class", "headline svelte-12dqoo3");
			attr(section, "class", "section-container svelte-12dqoo3");
		},
		m(target, anchor) {
			insert_hydration(target, section, anchor);
			append_hydration(section, h1);
			append_hydration(h1, t0);
			append_hydration(section, t1);
			if (if_block0) if_block0.m(section, null);
			append_hydration(section, t2);
			if (if_block1) if_block1.m(section, null);
			append_hydration(section, t3);
			if (if_block2) if_block2.m(section, null);
		},
		p(ctx, [dirty]) {
			if (dirty & /*heading*/ 1) set_data(t0, /*heading*/ ctx[0]);

			if (/*subheading*/ ctx[2]) {
				if (if_block0) {
					if_block0.p(ctx, dirty);
				} else {
					if_block0 = create_if_block_2(ctx);
					if_block0.c();
					if_block0.m(section, t2);
				}
			} else if (if_block0) {
				if_block0.d(1);
				if_block0 = null;
			}

			if (/*graphics*/ ctx[1].left) {
				if (if_block1) {
					if_block1.p(ctx, dirty);
				} else {
					if_block1 = create_if_block_1(ctx);
					if_block1.c();
					if_block1.m(section, t3);
				}
			} else if (if_block1) {
				if_block1.d(1);
				if_block1 = null;
			}

			if (/*graphics*/ ctx[1].right) {
				if (if_block2) {
					if_block2.p(ctx, dirty);
				} else {
					if_block2 = create_if_block(ctx);
					if_block2.c();
					if_block2.m(section, null);
				}
			} else if (if_block2) {
				if_block2.d(1);
				if_block2 = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(section);
			if (if_block0) if_block0.d();
			if (if_block1) if_block1.d();
			if (if_block2) if_block2.d();
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { props } = $$props;
	let { form } = $$props;
	let { heading } = $$props;
	let { graphics } = $$props;
	let { subheading } = $$props;

	$$self.$$set = $$props => {
		if ('props' in $$props) $$invalidate(3, props = $$props.props);
		if ('form' in $$props) $$invalidate(4, form = $$props.form);
		if ('heading' in $$props) $$invalidate(0, heading = $$props.heading);
		if ('graphics' in $$props) $$invalidate(1, graphics = $$props.graphics);
		if ('subheading' in $$props) $$invalidate(2, subheading = $$props.subheading);
	};

	return [heading, graphics, subheading, props, form];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance, create_fragment, safe_not_equal, {
			props: 3,
			form: 4,
			heading: 0,
			graphics: 1,
			subheading: 2
		});
	}
}

export { Component as default };
