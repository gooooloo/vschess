/*
 * 微思象棋播放器 V2.6.1
 * https://www.xiaxiangqi.com/
 *
 * Copyright @ 2009-2023 Margin.Top 版权所有
 * https://margin.top/
 *
 * 本程序遵循 LGPL 协议
 * https://www.gnu.org/licenses/lgpl.html
 *
 * ECCO 开局分类编号系统算法由象棋百科全书友情提供，在此表示衷心感谢。
 * https://www.xqbase.com/
 *
 * 选择器引擎选用 Qwery
 * https://github.com/ded/qwery/
 *
 * 最后修改日期：北京时间 2023年3月11日
 * Sat, 11 Mar 2023 20:01:37 +0800
 */

(function(){

// Qwery 选择器引擎
var Qwery;

(function () {
    var doc = document,
        html = doc.documentElement,
        byClass = 'getElementsByClassName',
        byTag = 'getElementsByTagName',
        qSA = 'querySelectorAll',
        useNativeQSA = 'useNativeQSA',
        tagName = 'tagName',
        nodeType = 'nodeType',
        select,
        id = /#([\w\-]+)/,
        clas = /\.[\w\-]+/g,
        idOnly = /^#([\w\-]+)$/,
        classOnly = /^\.([\w\-]+)$/,
        tagOnly = /^([\w\-]+)$/,
        tagAndOrClass = /^([\w]+)?\.([\w\-]+)$/,
        splittable = /(^|,)\s*[>~+]/,
        normalizr = /^\s+|\s*([,\s\+\~>]|$)\s*/g,
        splitters = /[\s\>\+\~]/,
        splittersMore = /(?![\s\w\-\/\?\&\=\:\.\(\)\!,@#%<>\{\}\$\*\^'"]*\]|[\s\w\+\-]*\))/,
        specialChars = /([.*+?\^=!:${}()|\[\]\/\\])/g,
        simple = /^(\*|[a-z0-9]+)?(?:([\.\#]+[\w\-\.#]+)?)/,
        attr = /\[([\w\-]+)(?:([\|\^\$\*\~]?\=)['"]?([ \w\-\/\?\&\=\:\.\(\)\!,@#%<>\{\}\$\*\^]+)["']?)?\]/,
        pseudo = /:([\w\-]+)(\(['"]?([^()]+)['"]?\))?/,
        easy = new RegExp(idOnly.source + '|' + tagOnly.source + '|' + classOnly.source),
        dividers = new RegExp('(' + splitters.source + ')' + splittersMore.source, 'g'),
        tokenizr = new RegExp(splitters.source + splittersMore.source),
        chunker = new RegExp(simple.source + '(' + attr.source + ')?' + '(' + pseudo.source + ')?');

    var walker = {
        ' ': function (node) { return node && node !== html && node.parentNode; },
        '>': function (node, contestant) { return node && node.parentNode == contestant.parentNode && node.parentNode; },
        '~': function (node) { return node && node.previousSibling; },
        '+': function (node, contestant, p1, p2) { if (!node) return false; return (p1 = previous(node)) && (p2 = previous(contestant)) && p1 == p2 && p1; }
    };

    function cache() {
        this.c = {};
    }

    cache.prototype = {
        g: function (k) { return this.c[k] || undefined; },
        s: function (k, v, r) { v = r ? new RegExp(v) : v; return (this.c[k] = v); }
    };

    var classCache = new cache(), cleanCache = new cache(), attrCache = new cache(), tokenCache = new cache();

    function classRegex(c) {
        return classCache.g(c) || classCache.s(c, '(^|\\s+)' + c + '(\\s+|$)', 1);
    }

    function each(a, fn) {
        var i = 0, l = a.length;
        for (; i < l; i++) fn(a[i]);
    }

    function flatten(ar) {
        for (var r = [], i = 0, l = ar.length; i < l; ++i) arrayLike(ar[i]) ? (r = r.concat(ar[i])) : (r[r.length] = ar[i]);
        return r;
    }

    function arrayify(ar) {
        var i = 0, l = ar.length, r = [];
        for (; i < l; i++) r[i] = ar[i];
        return r;
    }

    function previous(n) {
        while (n = n.previousSibling) if (n[nodeType] == 1) break;
        return n;
    }

    function q(query) {
        return query.match(chunker);
    }

    function interpret(whole, tag, idsAndClasses, wholeAttribute, attribute, qualifier, value, wholePseudo, pseudo, wholePseudoVal, pseudoVal) {
        var i, m, k, o, classes;

        if (this[nodeType] !== 1) {
            return false;
        }

        if (tag && tag !== '*' && this[tagName] && this[tagName].toLowerCase() !== tag) {
            return false;
        }

        if (idsAndClasses && (m = idsAndClasses.match(id)) && m[1] !== this.id) {
            return false;
        }

        if (idsAndClasses && (classes = idsAndClasses.match(clas))) {
            for (i = classes.length; i--;) {
                if (!classRegex(classes[i].slice(1)).test(this.className)) {
                    return false;
                }
            }
        }

        if (pseudo && qwery.pseudos[pseudo] && !qwery.pseudos[pseudo](this, pseudoVal)) {
            return false;
        }

        if (wholeAttribute && !value) {
            o = this.attributes;

            for (k in o) {
                if (Object.prototype.hasOwnProperty.call(o, k) && (o[k].name || k) == attribute) {
                    return this;
                }
            }
        }

        if (wholeAttribute && !checkAttr(qualifier, getAttr(this, attribute) || '', value)) {
            return false;
        }

        return this;
    }

    function clean(s) {
        return cleanCache.g(s) || cleanCache.s(s, s.replace(specialChars, '\\$1'));
    }

    function checkAttr(qualify, actual, val) {
        switch (qualify) {
            case '=' : return actual == val;
            case '^=': return actual.match(attrCache.g('^=' + val) || attrCache.s('^=' + val, '^'          + clean(val)               , 1));
            case '$=': return actual.match(attrCache.g('$=' + val) || attrCache.s('$=' + val,                clean(val) + '$'         , 1));
            case '*=': return actual.match(attrCache.g(       val) || attrCache.s(       val,                clean(val)               , 1));
            case '~=': return actual.match(attrCache.g('~=' + val) || attrCache.s('~=' + val, '(?:^|\\s+)' + clean(val) + '(?:\\s+|$)', 1));
            case '|=': return actual.match(attrCache.g('|=' + val) || attrCache.s('|=' + val, '^'          + clean(val) + '(-|$)'     , 1));
        }

        return 0;
    }

    function _qwery(selector, _root) {
        var r = [], ret = [], i, l, m, token, tag, els, intr, item, root = _root;
        var tokens = tokenCache.g(selector) || tokenCache.s(selector, selector.split(tokenizr));
        var dividedTokens = selector.match(dividers);

        if (!tokens.length) {
            return r;
        }

        token = (tokens = tokens.slice(0)).pop();

        if (tokens.length && (m = tokens[tokens.length - 1].match(idOnly))) {
            root = byId(_root, m[1]);
        }

        if (!root) {
            return r;
        }

        intr = q(token);
        els = root !== _root && root[nodeType] !== 9 && dividedTokens && /^[+~]$/.test(dividedTokens[dividedTokens.length - 1]) ?
            function (r) {
                while (root = root.nextSibling) {
                    root[nodeType] == 1 && (intr[1] ? intr[1] == root[tagName].toLowerCase() : 1) && (r[r.length] = root)
                }
                return r
            }([]) :
            root[byTag](intr[1] || '*');

        for (i = 0, l = els.length; i < l; i++) {
            if (item = interpret.apply(els[i], intr)) r[r.length] = item;
        }

        if (!tokens.length) {
            return r;
        }

        each(r, function (e) {
            if (ancestorMatch(e, tokens, dividedTokens)) {
                ret[ret.length] = e;
            }
        });

        return ret;
    }

    function is(el, selector, root) {
        if (isNode(selector)) {
            return el == selector;
        }

        if (arrayLike(selector)) {
            return !!~flatten(selector).indexOf(el);
        }

        var selectors = selector.split(','), tokens, dividedTokens;

        while (selector = selectors.pop()) {
            tokens = tokenCache.g(selector) || tokenCache.s(selector, selector.split(tokenizr));
            dividedTokens = selector.match(dividers);
            tokens = tokens.slice(0);

            if (interpret.apply(el, q(tokens.pop())) && (!tokens.length || ancestorMatch(el, tokens, dividedTokens, root))) {
                return true;
            }
        }

        return false;
    }

    function ancestorMatch(el, tokens, dividedTokens, root) {
        var cand;

        function crawl(e, i, p) {
            while (p = walker[dividedTokens[i]](p, e)) {
                if (isNode(p) && (interpret.apply(p, q(tokens[i])))) {
                    if (i) {
                        if (cand = crawl(p, i - 1, p)) {
                            return cand;
                        }
                    }
                    else {
                        return p;
                    }
                }
            }
        }

        return (cand = crawl(el, tokens.length - 1, el)) && (!root || isAncestor(cand, root));
    }

    function isNode(el, t) {
        return el && typeof el === 'object' && (t = el[nodeType]) && (t == 1 || t == 9);
    }

    function uniq(ar) {
        var a = [], i, j;

        o: for (i = 0; i < ar.length; ++i) {
            for (j = 0; j < a.length; ++j) {
                if (a[j] == ar[i]) {
                    continue o;
                }
            }

            a[a.length] = ar[i];
        }

        return a;
    }

    function arrayLike(o) {
        return (typeof o === 'object' && isFinite(o.length));
    }

    function normalizeRoot(root) {
        if (!root) {
            return doc;
        }

        if (typeof root == 'string') {
            return qwery(root)[0];
        }

        if (!root[nodeType] && arrayLike(root)) {
            return root[0];
        }

        return root;
    }

    function byId(root, id, el) {
        return root[nodeType] === 9 ? root.getElementById(id) :
            root.ownerDocument &&
            (((el = root.ownerDocument.getElementById(id)) && isAncestor(el, root) && el) ||
            (!isAncestor(root, root.ownerDocument) && select('[id="' + id + '"]', root)[0]));
    }

    function qwery(selector, _root) {
        var m, el, root = normalizeRoot(_root);

        if (!root || !selector) {
            return [];
        }

        if (selector === window || isNode(selector)) {
            return !_root || (selector !== window && isNode(root) && isAncestor(selector, root)) ? [selector] : [];
        }

        if (selector && arrayLike(selector)) {
            return flatten(selector);
        }

        if (m = selector.match(easy)) {
            if (m[1]) {
                return (el = byId(root, m[1])) ? [el] : [];
            }

            if (m[2]) {
                return arrayify(root[byTag](m[2]));
            }

            if (hasByClass && m[3]) {
                return arrayify(root[byClass](m[3]));
            }
        }

        return select(selector, root);
    }

    function collectSelector(root, collector) {
        return function (s) {
            var oid, nid;

            if (splittable.test(s)) {
                if (root[nodeType] !== 9) {
                    if (!(nid = oid = root.getAttribute('id'))) {
                        root.setAttribute('id', nid = '__qwerymeupscotty');
                    }

                    s = '[id="' + nid + '"]' + s;
                    collector(root.parentNode || root, s, true);
                    oid || root.removeAttribute('id');
                }

                return;
            }

            s.length && collector(root, s, false);
        }
    }

    var isAncestor = 'compareDocumentPosition' in html ?
        function (element, container) {
            return (container.compareDocumentPosition(element) & 16) == 16;
        } : 'contains' in html ?
        function (element, container) {
            container = container[nodeType] === 9 || container == window ? html : container;
            return container !== element && container.contains(element);
        } :
        function (element, container) {
            while (element = element.parentNode) if (element === container) return 1;
            return 0;
        },
        getAttr = function () {
            var e = doc.createElement('p');
            return ((e.innerHTML = '<a href="#x">x</a>') && e.firstChild.getAttribute('href') != '#x') ?
                function (e, a) {
                    return a === 'class' ? e.className : (a === 'href' || a === 'src') ?
                    e.getAttribute(a, 2) : e.getAttribute(a);
            } :
            function (e, a) { return e.getAttribute(a); };
        }(),
    hasByClass = !!doc[byClass],
    hasQSA = doc.querySelector && doc[qSA],
    selectQSA = function (selector, root) {
        var result = [], ss, e;

        try {
            if (root[nodeType] === 9 || !splittable.test(selector)) {
                return arrayify(root[qSA](selector));
            }

            each(ss = selector.split(','), collectSelector(root, function (ctx, s) {
                e = ctx[qSA](s);
                if (e.length == 1) {
                    result[result.length] = e.item(0);
                }
                else if (e.length) {
                    result = result.concat(arrayify(e));
                }
            }));

            return ss.length > 1 && result.length > 1 ? uniq(result) : result;
        }
        catch (ex) {}
        return selectNonNative(selector, root);
    },
    selectNonNative = function (selector, root) {
        var result = [], items, m, i, l, r, ss;
        selector = selector.replace(normalizr, '$1');

        if (m = selector.match(tagAndOrClass)) {
            r = classRegex(m[2]);
            items = root[byTag](m[1] || '*');

            for (i = 0, l = items.length; i < l; i++) {
                if (r.test(items[i].className)) {
                    result[result.length] = items[i];
                }
            }

            return result;
        }

        each(ss = selector.split(','), collectSelector(root, function (ctx, s, rewrite) {
            r = _qwery(s, ctx);

            for (i = 0, l = r.length; i < l; i++) {
                if (ctx[nodeType] === 9 || rewrite || isAncestor(r[i], root)) {
                    result[result.length] = r[i];
                }
            }
        }));

        return ss.length > 1 && result.length > 1 ? uniq(result) : result;
    },
    configure = function (options) {
        if (typeof options[useNativeQSA] !== 'undefined') {
            select = !options[useNativeQSA] ? selectNonNative : hasQSA ? selectQSA : selectNonNative;
        }
    };

    configure({ useNativeQSA: true });

    qwery.configure = configure;
    qwery.uniq = uniq;
    qwery.is = is;
    qwery.pseudos = {};

    Qwery = qwery;
})();

// 从 V2.4.0 版开始，播放器不再依赖 Zepto/jQuery 框架。
// 模拟 Zepto/jQuery，仅限于播放器内部使用，因为我只模拟了播放器中用到的方法，没用到的方法没有模拟。
var $ = function(selector) {
    return new $.init(selector);
};

$.init = function(selector) {
    this.length = 0;

    if (!selector) {
        return this;
    }

    if (selector instanceof $.init) {
        return selector;
    }

    if (selector.nodeType) {
        this[0] = selector;
        this.length = 1;
        return this;
    }

    if (typeof selector === "object" && typeof selector.length === "number") {
        var list = selector;
    }
    else if (typeof selector === "string") {
        if (~selector.indexOf("<")) {
            var wrap = document.createElement("div"), list = [];
            wrap.innerHTML = selector;

            for (var i = 0; i < wrap.childNodes.length; ++i) {
                wrap.childNodes[i].nodeType === 1 && list.push(wrap.childNodes[i]);
            }
        }
        else {
            var list = Qwery(selector);
        }
    }
    else {
        var list = [];
    }

    this.length = list.length;

    for (var i = 0; i < list.length; ++i) {
        this[i] = list[i];
    }

    return this;
};

$.expand = $.init.prototype;

$.expand.not = function(selector){
    var notList = Qwery(selector);
    var newList = [];

    for (var i = 0; i < this.length; ++i) {
        ~notList.indexOf(this[i]) || newList.push(this[i]);
    }

    return $(newList);
};

$.expand.eq = function(index){
    return this.length ? $(this[index]) : $();
};

$.expand.first = function(){
    return this.length ? $(this[0]) : $();
};

$.expand.last = function(){
    return this.length ? $(this[this.length - 1]) : $();
};

$.expand.clone = function(){
    return this.length ? $(this[0].cloneNode(true)) : $();
};

$.expand.after = function(selector){
    for (var i = 0; i < this.length; ++i) {
        var next   = this[i].nextSibling;
        var parent = this[i].parentNode ;
        var list   = $(selector);

        for (var j = 0; j < list.length; ++j) {
            parent.insertBefore(list[i], next);
        }
    }

    return this;
};

$.expand.addClass = function(className){
    if (!className) {
        return this;
    }

    var addList = $.trim(className).split(/[\s]+/);

    if (this[0] && this[0].classList) {
        for (var i = 0; i < this.length; ++i) {
            for (var j = 0; j < addList.length; ++j) {
                this[i].classList.add(addList[j]);
            }
        }
    }
    else {
        for (var i = 0; i < this.length; ++i) {
            var classNameList = $.trim(this[i].className).split(/[\s]+/);

            for (var j = 0; j < addList.length; ++j) {
                ~classNameList.indexOf(addList[j]) || classNameList.push(addList[j]);
            }

            this[i].className = classNameList.join(" ");
        }
    }

    return this;
};

$.expand.removeClass = function(className){
    if (!className) {
        for (var i = 0; i < this.length; ++i) {
            this[i].className = "";
        }

        return this;
    }

    var removeList = $.trim(className).split(/[\s]+/);

    if (this[0] && this[0].classList) {
        for (var i = 0; i < this.length; ++i) {
            for (var j = 0; j < removeList.length; ++j) {
                this[i].classList.remove(removeList[j]);
            }
        }
    }
    else {
        for (var i = 0; i < this.length; ++i) {
            var classNameList = $.trim(this[i].className).split(/[\s]+/);
            var resultList = [];

            for (var j = 0; j < classNameList.length; ++j) {
                ~removeList.indexOf(classNameList[j]) || resultList.push(classNameList[j]);
            }

            this[i].className = resultList.join(" ");
        }
    }

    return this;
};

$.expand.toggleClass = function(className){
    if (!className) {
        return this;
    }

    var toggleList = $.trim(className).split(/[\s]+/);

    if (this[0] && this[0].classList) {
        for (var i = 0; i < this.length; ++i) {
            for (var j = 0; j < toggleList.length; ++j) {
                this[i].classList.toggle(toggleList[j]);
            }
        }
    }
    else {
        for (var i = 0; i < this.length; ++i) {
            var _this = $(this[i]);

            for (var j = 0; j < toggleList.length; ++j) {
                _this.hasClass(toggleList[j]) ? _this.removeClass(toggleList[j]) : _this.addClass(toggleList[j]);
            }
        }
    }

    return this;
};

$.expand.hasClass = function(className){
    if (this.length === 0) {
        return false;
    }

    var classNameList = $.trim(this[0].className).split(/[\s]+/);
    return !!~classNameList.indexOf(className);
};

$.expand.html = function(){
    if (arguments.length) {
        for (var i = 0; i < this.length; ++i) {
            this[i].innerHTML = arguments[0];
        }

        return this;
    }
    else {
        return this.length ? this[0].innerHTML : "";
    }
};

$.expand.text = function(){
    if (arguments.length) {
        for (var i = 0; i < this.length; ++i) {
            this[i].innerHTML = "";
            this[i].appendChild(document.createTextNode(arguments[0]));
        }

        return this;
    }
    else {
        if (this.length) {
            var getText = function(elem) {
        		var node, ret = "", i = 0, nodeType = elem.nodeType;

        		if (!nodeType) {
        			while ((node = elem[i++])) {
        				ret += getText(node);
        			}
        		}
                else if (nodeType === 1 || nodeType === 9 || nodeType === 11) {
        			if (typeof elem.textContent === "string") {
        				return elem.textContent;
        			}
                    else {
        				for (elem = elem.firstChild; elem; elem = elem.nextSibling) {
        					ret += getText(elem);
        				}
        			}
        		}
                else if (nodeType === 3 || nodeType === 4) {
        			return elem.nodeValue;
        		}

        		return ret;
        	};

            var elem = this[0];
            var node, ret = "", i = 0, nodeType = elem.nodeType;

            if (!nodeType) {
                while ((node = elem[i++])) {
                    ret += getText(node);
                }
            }
            else if (nodeType === 1 || nodeType === 9 || nodeType === 11) {
                if (typeof elem.textContent === "string") {
                    return elem.textContent;
                }
                else {
                    for (elem = elem.firstChild; elem; elem = elem.nextSibling) {
                        ret += getText(elem);
                    }
                }
            }
            else if (nodeType === 3 || nodeType === 4) {
                return elem.nodeValue;
            }

            return ret;
        }
        else {
            return "";
        }
    }
};

$.expand.empty = function(){
    return this.html("");
};

$.expand.attr = function(attr){
    if (arguments.length > 1) {
        for (var i = 0; i < this.length; ++i) {
            this[i].setAttribute(attr, arguments[1]);
        }

        return this;
    }
    else {
        if (typeof attr === "object") {
            for (var i = 0; i < this.length; ++i) {
                for (var j in attr) {
                    this[i].setAttribute(j, attr[j]);
                }
            }

            return this;
        }
        else {
            return this.length ? this[0].getAttribute(attr) : "";
        }
    }
};

$.expand.removeAttr = function(attr){
    for (var i = 0; i < this.length; ++i) {
        this[i].removeAttribute(attr);
    }

    return this;
};

$.expand.data = function(){
    if (arguments.length > 1) {
        return this.attr("data-" + arguments[0], arguments[1]);
    }
    else {
        return this.attr("data-" + arguments[0]);
    }
};

$.expand.children = function(selector){
    var result = [];

    for (var i = 0; i < this.length; ++i) {
        if (typeof selector === "string") {
            var list = Qwery(">" + selector, this[i]);
        }
        else {
            var list = this[i].childNodes;
        }

        for (var j = 0; j < list.length; ++j) {
            list[j].nodeType === 1 && result.push(list[j]);
        }
    }

    return $(result);
};

$.expand.remove = function(){
    for (var i = 0; i < this.length; ++i) {
        this[i].parentNode.removeChild(this[i]);
    }

    return this;
};

$.expand.bind = function(event, func){
    var eventList = event.split(" ");

    for (var i = 0; i < eventList.length; ++i) {
        for (var j = 0; j < this.length; ++j) {
            if (document.addEventListener) {
                this[j].addEventListener(eventList[i], func);
            }
            else {
                this[j].attachEvent(eventList[i], func);
            }
        }
    }

    return this;
};

$.expand.trigger = function(event){
    ~["click", "submit"].indexOf(event) || (event = "click");

    for (var i = 0; i < this.length; ++i) {
        this[i][event]();
    }

    return this;
};

$.expand.append = function(selector){
    for (var i = 0; i < this.length; ++i) {
        var list = $(selector);

        for (var j = 0; j < list.length; ++j) {
            this[i].appendChild(list[j]);
        }
    }

    return this;
};

$.expand.each = function(func){
    for (var i = 0; i < this.length; ++i) {
        func.call(this[i], i, this[i]);
    }

    return this;
};

$.expand.appendTo = function(selector){
    for (var i = 0; i < this.length; ++i) {
        var list = $(selector);

        for (var j = 0; j < list.length; ++j) {
            list[i].appendChild(this[i]);
        }
    }

    return this;
};

$.expand.css = function(config){
    for (var i = 0; i < this.length; ++i) {
        for (var j in config) {
            var key = j;
            var value = config[j];

            key = key.replace(/-webkit-t/g, "webkitT");
            key = key.replace(   /-moz-t/g,    "mozT");
            key = key.replace(    /-ms-t/g,     "msT");
            key = key.replace(     /-o-t/g,      "oT");

            ~"height width top right bottom left marginTop marginRight marginBottom marginLeft paddingTop paddingRight paddingBottom paddingLeft".split(" ").indexOf(j) && !isNaN(+config[j]) && (value += "px");

            this[i].style[key] = value;
        }
    }

    return this;
};

$.expand.filter = function(selector){
    var filterList = $.trim(selector.replace(/\./g, "")).split(/[\s]+/);
    var result = [];

    for (var i = 0; i < this.length; ++i) {
        var classNameList = $.trim(this[i].className).split(/[\s]+/);

        for (var j = 0; j < classNameList.length; ++j) {
            if (~filterList.indexOf(classNameList[j])) {
                result.push(this[i]);
                break;
            }
        }
    }

    return $(result);
};

$.expand.val = function(){
    if (arguments.length) {
        for (var i = 0; i < this.length; ++i) {
            this[i].value = arguments[0];
        }

        return this;
    }
    else {
        return this.length ? this[0].value : "";
    }
};

$.expand.height = function(){
    if (arguments.length) {
        for (var i = 0; i < this.length; ++i) {
            this[i].style.height = arguments[0] + "px";
        }

        return this;
    }
    else {
        return this.length ? this[0].offsetHeight : 0;
    }
};

$.expand.width = function(){
    if (arguments.length) {
        for (var i = 0; i < this.length; ++i) {
            this[i].style.width = arguments[0] + "px";
        }

        return this;
    }
    else {
        return this.length ? this[0].offsetWidth : 0;
    }
};

$.expand.scrollTop = function(){
    if (arguments.length) {
        for (var i = 0; i < this.length; ++i) {
            this[i].scrollTop = arguments[0];
        }

        return this;
    }
    else {
        return this.length ? this[0].scrollTop : 0;
    }
};

$.expand.scrollLeft = function(){
    if (arguments.length) {
        for (var i = 0; i < this.length; ++i) {
            this[i].scrollLeft = arguments[0];
        }

        return this;
    }
    else {
        return this.length ? this[0].scrollLeft : 0;
    }
};

$.expand.position = function(){
    if (!this.length) {
        return { top: 0, left: 0 };
    }

    var   selfPosition = this[0]           .getBoundingClientRect();
    var parentPosition = this[0].parentNode.getBoundingClientRect();
    var sl =   selfPosition.left;
    var st =   selfPosition.top ;
    var pl = parentPosition.left;
    var pt = parentPosition.top ;
    return { top: st - pt, left: sl - pl };
};

$.expand.show = function(){
    for (var i = 0; i < this.length; ++i) {
        this[i].style.display = "block";
    }

    return this;
};

$.expand.hide = function(){
    for (var i = 0; i < this.length; ++i) {
        this[i].style.display = "none";
    }

    return this;
};

$.expand.animate = function(config, time, callback){
    this._config   = config;
    this._time     = time;
    this._callback = callback;
    this._start    = new Date().getTime();
    this._param    = [];

    for (var i = 0; i < this.length; ++i) {
        this._param[i] = $(this[i]).position();
    }

    var _this = this;
    this._nextFrame = setTimeout(function(){ _this.nextFrame(); }, vschess.threadTimeout);
    return this;
};

$.expand.nextFrame = function(){
    var time = new Date().getTime();
    var deltaTime = time - this._start;
    var deltaPercent = deltaTime / this._time;

    if (deltaTime >= this._time) {
        this.stop();
    }
    else {
        for (var i = 0; i < this.length; ++i) {
            var targetTop  = this._param[i].top  + (this._config.top  - this._param[i].top ) * deltaPercent;
            var targetLeft = this._param[i].left + (this._config.left - this._param[i].left) * deltaPercent;
            this[i].style.top  = targetTop  + "px";
            this[i].style.left = targetLeft + "px";
        }

        var _this = this;
        this._nextFrame = setTimeout(function(){ _this.nextFrame(); }, vschess.threadTimeout);
    }

    return this;
};

$.expand.stop = function(){
    clearTimeout(this._nextFrame);

    for (var i = 0; i < this.length; ++i) {
        this[i].style.top  = this._config.top  + "px";
        this[i].style.left = this._config.left + "px";
    }

    typeof this._callback === "function" && this._callback();
    delete this._config;
    delete this._time;
    delete this._callback;
    delete this._start;
    delete this._param;
    delete this._nextFrame;
    return this;
};

$.extend = function(){
    var arg = arguments;

    if (arg[0] === true) {
        if (typeof arg[1] !== "object") {
            return {};
        }

        for (var i = 2; i < arg.length; ++i) {
            if (typeof arg[i] !== "object") {
                continue;
            }

            for (var j in arg[i]) {
                if (typeof arg[1][j] === "object" && typeof arg[i][j] === "object") {
                    $.extend(true, arg[1][j], arg[i][j]);
                }
                else {
                    arg[1][j] = arg[i][j];
                }
            }
        }

        return arg[1];
    }
    else {
        if (typeof arg[0] !== "object") {
            return {};
        }

        for (var i = 1; i < arg.length; ++i) {
            if (typeof arg[i] === "object") {
                for (var j in arg[i]) {
                    arg[0][j] = arg[i][j];
                }
            }
        }

        return arg[0];
    }
};

$.each = function(arr, func){
    for (var i in arr) {
        func.call(arr[i], i, arr[i]);
    }

    return this;
};

$.trim = function(str){
    return (str || "").replace(/^\s+|\s+$/gm, "");
};

$.uniqid = 0;

$.ajax = function(config){
    var cfg = { url: "", type: "POST", data: {}, dataType: "json" };
    cfg = $.extend(true, {}, cfg, config);
    typeof cfg.success === "function" || (cfg.success = function(){});
    typeof cfg.error   === "function" || (cfg.error   = function(){});

    if (cfg.dataType === "jsonp") {
        var callbackName = "vschess_callback_" + new Date().getTime() + "_" + $.uniqid++;
        var tag  = document.createElement("script");
        var mask = ~cfg.url.indexOf("?") ? "&" : "?";
        tag.src  =  cfg.url + mask + "callback=" + callbackName + "&" + new Date().getTime();

        window[callbackName] = function(response){
            cfg.success(response);
            delete window[callbackName];
            document.getElementsByTagName("body")[0].removeChild(tag);
        };

        document.getElementsByTagName("body")[0].appendChild(tag);
    }
    else {
        var xhrs = [
            function(){ return new XMLHttpRequest(); },
            function(){ return new ActiveXObject("Microsoft.XMLHTTP" ); },
            function(){ return new ActiveXObject("MSXML2.XMLHTTP.3.0"); },
            function(){ return new ActiveXObject("MSXML2.XMLHTTP"    ); }
        ];

        var xhr = false;

        for (var i = 0; i < xhrs.length; ++i) {
            try {
                xhr = xhrs[i]();
                break;
            }
            catch (e) {
            }
        }

        if (!xhr) {
            cfg.error();
            return false;
        }

        xhr.open(cfg.type.toUpperCase(), cfg.url);
        xhr.setRequestHeader("Content-Type", "application/x-www-form-urlencoded");

        var data = [];

        for (var i in cfg.data) {
            data.push(i + "=" + encodeURIComponent(cfg.data[i]));
        }

        xhr.send(data.join("&"));

        xhr.onreadystatechange = function(){
            if (xhr.readyState === 4 && xhr.status === 200) {
                if (typeof xhr.responseText === "string" && cfg.dataType === "json") {
                    cfg.success($.parseJSON(xhr.responseText));
                }
                else {
                    cfg.success(xhr.responseText);
                }
            }
        };
    }

    return true;
};

$.parseJSON = function(json){
    if (JSON && typeof JSON.parse === "function") {
        return JSON.parse(json);
    }
    else {
        return eval("(" + json + ")");
    }
};

// 主程序
var vschess = {
	// 当前版本号
	version: "2.6.1",

	// 版本时间戳
	timestamp: "Sat, 11 Mar 2023 20:01:37 +0800",

	// 默认局面，使用 16x16 方式存储数据，虽然浪费空间，但是便于运算，效率较高
	// situation[0] 表示的是当前走棋方，1 为红方，2 为黑方
	// situation[1] 表示的是当前回合数
	// 其余部分 0 表示棋盘外面，1 表示该位置没有棋子
	// 棋子标识采用 16 进制方式计算，如 21 为十六进制的 15，1 表示红方，与 situation[0] 对应，5 表示帅（将）
	// 1:车 2:马 3:相（象） 4:仕（士） 5:帅（将） 6:炮 7:兵（卒）
	situation: [
		1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0,33,34,35,36,37,36,35,34,33, 0, 0, 0, 0,
		0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0,
		0, 0, 0, 1,38, 1, 1, 1, 1, 1,38, 1, 0, 0, 0, 0,
		0, 0, 0,39, 1,39, 1,39, 1,39, 1,39, 0, 0, 0, 0,
		0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0,
		0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0,
		0, 0, 0,23, 1,23, 1,23, 1,23, 1,23, 0, 0, 0, 0,
		0, 0, 0, 1,22, 1, 1, 1, 1, 1,22, 1, 0, 0, 0, 0,
		0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0,
		0, 0, 0,17,18,19,20,21,20,19,18,17, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
	],

	// 九宫格
	castle: [
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
		0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
	],

	// 九宫格索引
	castleR: [166, 167, 168, 182, 183, 184, 198, 199, 200], // 帅
	castleB: [ 54,  55,  56,  70,  71,  72,  86,  87,  88], // 将

	// 帅(将)的步长
	kingDelta: [-16, -1, 1, 16],

	// 仕(士)的步长
	advisorDelta: [-17, -15, 15, 17],

	// 马的步长，以帅(将)的步长作为马腿
	knightDelta: [[-33, -31], [-18, 14], [-14, 18], [31, 33]],

	// 被马将军的步长，以仕(士)的步长作为马腿
	knightCheckDelta: [[-33, -18], [-31, -14], [14, 31], [18, 33]],

	// 棋盘转换为局面，就是不同格式之间的映射，下同
	b2s: [
		 51,  52,  53,  54,  55,  56,  57,  58,  59,
		 67,  68,  69,  70,  71,  72,  73,  74,  75,
		 83,  84,  85,  86,  87,  88,  89,  90,  91,
		 99, 100, 101, 102, 103, 104, 105, 106, 107,
		115, 116, 117, 118, 119, 120, 121, 122, 123,
		131, 132, 133, 134, 135, 136, 137, 138, 139,
		147, 148, 149, 150, 151, 152, 153, 154, 155,
		163, 164, 165, 166, 167, 168, 169, 170, 171,
		179, 180, 181, 182, 183, 184, 185, 186, 187,
		195, 196, 197, 198, 199, 200, 201, 202, 203
	],

	// 局面转换为棋盘
	s2b: [
		0, 0, 0,  0,  0,  0,  0,  0,  0,  0,  0,  0, 0, 0, 0, 0,
		0, 0, 0,  0,  0,  0,  0,  0,  0,  0,  0,  0, 0, 0, 0, 0,
		0, 0, 0,  0,  0,  0,  0,  0,  0,  0,  0,  0, 0, 0, 0, 0,
		0, 0, 0,  0,  1,  2,  3,  4,  5,  6,  7,  8, 0, 0, 0, 0,
		0, 0, 0,  9, 10, 11, 12, 13, 14, 15, 16, 17, 0, 0, 0, 0,
		0, 0, 0, 18, 19, 20, 21, 22, 23, 24, 25, 26, 0, 0, 0, 0,
		0, 0, 0, 27, 28, 29, 30, 31, 32, 33, 34, 35, 0, 0, 0, 0,
		0, 0, 0, 36, 37, 38, 39, 40, 41, 42, 43, 44, 0, 0, 0, 0,
		0, 0, 0, 45, 46, 47, 48, 49, 50, 51, 52, 53, 0, 0, 0, 0,
		0, 0, 0, 54, 55, 56, 57, 58, 59, 60, 61, 62, 0, 0, 0, 0,
		0, 0, 0, 63, 64, 65, 66, 67, 68, 69, 70, 71, 0, 0, 0, 0,
		0, 0, 0, 72, 73, 74, 75, 76, 77, 78, 79, 80, 0, 0, 0, 0,
		0, 0, 0, 81, 82, 83, 84, 85, 86, 87, 88, 89, 0, 0, 0, 0,
		0, 0, 0,  0,  0,  0,  0,  0,  0,  0,  0,  0, 0, 0, 0, 0,
		0, 0, 0,  0,  0,  0,  0,  0,  0,  0,  0,  0, 0, 0, 0, 0,
		0, 0, 0,  0,  0,  0,  0,  0,  0,  0,  0,  0, 0, 0, 0, 0
	],

	// 棋盘转换为 ICCS
	b2i: [
		"a9", "b9", "c9", "d9", "e9", "f9", "g9", "h9", "i9",
		"a8", "b8", "c8", "d8", "e8", "f8", "g8", "h8", "i8",
		"a7", "b7", "c7", "d7", "e7", "f7", "g7", "h7", "i7",
		"a6", "b6", "c6", "d6", "e6", "f6", "g6", "h6", "i6",
		"a5", "b5", "c5", "d5", "e5", "f5", "g5", "h5", "i5",
		"a4", "b4", "c4", "d4", "e4", "f4", "g4", "h4", "i4",
		"a3", "b3", "c3", "d3", "e3", "f3", "g3", "h3", "i3",
		"a2", "b2", "c2", "d2", "e2", "f2", "g2", "h2", "i2",
		"a1", "b1", "c1", "d1", "e1", "f1", "g1", "h1", "i1",
		"a0", "b0", "c0", "d0", "e0", "f0", "g0", "h0", "i0"
	],

	// ICCS 转换为棋盘
	i2b: {
		a9:  0, b9:  1, c9:  2, d9:  3, e9:  4, f9:  5, g9:  6, h9:  7, i9:  8,
		a8:  9, b8: 10, c8: 11, d8: 12, e8: 13, f8: 14, g8: 15, h8: 16, i8: 17,
		a7: 18, b7: 19, c7: 20, d7: 21, e7: 22, f7: 23, g7: 24, h7: 25, i7: 26,
		a6: 27, b6: 28, c6: 29, d6: 30, e6: 31, f6: 32, g6: 33, h6: 34, i6: 35,
		a5: 36, b5: 37, c5: 38, d5: 39, e5: 40, f5: 41, g5: 42, h5: 43, i5: 44,
		a4: 45, b4: 46, c4: 47, d4: 48, e4: 49, f4: 50, g4: 51, h4: 52, i4: 53,
		a3: 54, b3: 55, c3: 56, d3: 57, e3: 58, f3: 59, g3: 60, h3: 61, i3: 62,
		a2: 63, b2: 64, c2: 65, d2: 66, e2: 67, f2: 68, g2: 69, h2: 70, i2: 71,
		a1: 72, b1: 73, c1: 74, d1: 75, e1: 76, f1: 77, g1: 78, h1: 79, i1: 80,
		a0: 81, b0: 82, c0: 83, d0: 84, e0: 85, f0: 86, g0: 87, h0: 88, i0: 89
	},

	// 局面转换为 ICCS
	s2i: [
		0, 0, 0,    0,    0,    0,    0,    0,    0,    0,    0,    0, 0, 0, 0, 0,
		0, 0, 0,    0,    0,    0,    0,    0,    0,    0,    0,    0, 0, 0, 0, 0,
		0, 0, 0,    0,    0,    0,    0,    0,    0,    0,    0,    0, 0, 0, 0, 0,
		0, 0, 0, "a9", "b9", "c9", "d9", "e9", "f9", "g9", "h9", "i9", 0, 0, 0, 0,
		0, 0, 0, "a8", "b8", "c8", "d8", "e8", "f8", "g8", "h8", "i8", 0, 0, 0, 0,
		0, 0, 0, "a7", "b7", "c7", "d7", "e7", "f7", "g7", "h7", "i7", 0, 0, 0, 0,
		0, 0, 0, "a6", "b6", "c6", "d6", "e6", "f6", "g6", "h6", "i6", 0, 0, 0, 0,
		0, 0, 0, "a5", "b5", "c5", "d5", "e5", "f5", "g5", "h5", "i5", 0, 0, 0, 0,
		0, 0, 0, "a4", "b4", "c4", "d4", "e4", "f4", "g4", "h4", "i4", 0, 0, 0, 0,
		0, 0, 0, "a3", "b3", "c3", "d3", "e3", "f3", "g3", "h3", "i3", 0, 0, 0, 0,
		0, 0, 0, "a2", "b2", "c2", "d2", "e2", "f2", "g2", "h2", "i2", 0, 0, 0, 0,
		0, 0, 0, "a1", "b1", "c1", "d1", "e1", "f1", "g1", "h1", "i1", 0, 0, 0, 0,
		0, 0, 0, "a0", "b0", "c0", "d0", "e0", "f0", "g0", "h0", "i0", 0, 0, 0, 0,
		0, 0, 0,    0,    0,    0,    0,    0,    0,    0,    0,    0, 0, 0, 0, 0,
		0, 0, 0,    0,    0,    0,    0,    0,    0,    0,    0,    0, 0, 0, 0, 0,
		0, 0, 0,    0,    0,    0,    0,    0,    0,    0,    0,    0, 0, 0, 0, 0
	],

	// ICCS 转换为局面
	i2s: {
		a9:  51, b9:  52, c9:  53, d9:  54, e9:  55, f9:  56, g9:  57, h9:  58, i9:  59,
		a8:  67, b8:  68, c8:  69, d8:  70, e8:  71, f8:  72, g8:  73, h8:  74, i8:  75,
		a7:  83, b7:  84, c7:  85, d7:  86, e7:  87, f7:  88, g7:  89, h7:  90, i7:  91,
		a6:  99, b6: 100, c6: 101, d6: 102, e6: 103, f6: 104, g6: 105, h6: 106, i6: 107,
		a5: 115, b5: 116, c5: 117, d5: 118, e5: 119, f5: 120, g5: 121, h5: 122, i5: 123,
		a4: 131, b4: 132, c4: 133, d4: 134, e4: 135, f4: 136, g4: 137, h4: 138, i4: 139,
		a3: 147, b3: 148, c3: 149, d3: 150, e3: 151, f3: 152, g3: 153, h3: 154, i3: 155,
		a2: 163, b2: 164, c2: 165, d2: 166, e2: 167, f2: 168, g2: 169, h2: 170, i2: 171,
		a1: 179, b1: 180, c1: 181, d1: 182, e1: 183, f1: 184, g1: 185, h1: 186, i1: 187,
		a0: 195, b0: 196, c0: 197, d0: 198, e0: 199, f0: 200, g0: 201, h0: 202, i0: 203
	},

	// 棋子标识转换为 Fen 字符
	n2f: "*****************RNBAKCP*********rnbakcp".split(""),

	// Fen 字符转换为棋子标识
	f2n: { R: 17, N: 18, H: 18, B: 19, E: 19, A: 20, K: 21, C: 22, P: 23, r: 33, n: 34, h: 34, b: 35, e: 35, a: 36, k: 37, c: 38, p: 39, "*": 1 },

	// 棋盘方向映射
	turn: [
		[
			 0,  1,  2,  3,  4,  5,  6,  7,  8,
			 9, 10, 11, 12, 13, 14, 15, 16, 17,
			18, 19, 20, 21, 22, 23, 24, 25, 26,
			27, 28, 29, 30, 31, 32, 33, 34, 35,
			36, 37, 38, 39, 40, 41, 42, 43, 44,
			45, 46, 47, 48, 49, 50, 51, 52, 53,
			54, 55, 56, 57, 58, 59, 60, 61, 62,
			63, 64, 65, 66, 67, 68, 69, 70, 71,
			72, 73, 74, 75, 76, 77, 78, 79, 80,
			81, 82, 83, 84, 85, 86, 87, 88, 89
		],
		[
			 8,  7,  6,  5,  4,  3,  2,  1,  0,
			17, 16, 15, 14, 13, 12, 11, 10,  9,
			26, 25, 24, 23, 22, 21, 20, 19, 18,
			35, 34, 33, 32, 31, 30, 29, 28, 27,
			44, 43, 42, 41, 40, 39, 38, 37, 36,
			53, 52, 51, 50, 49, 48, 47, 46, 45,
			62, 61, 60, 59, 58, 57, 56, 55, 54,
			71, 70, 69, 68, 67, 66, 65, 64, 63,
			80, 79, 78, 77, 76, 75, 74, 73, 72,
			89, 88, 87, 86, 85, 84, 83, 82, 81
		],
		[
			81, 82, 83, 84, 85, 86, 87, 88, 89,
			72, 73, 74, 75, 76, 77, 78, 79, 80,
			63, 64, 65, 66, 67, 68, 69, 70, 71,
			54, 55, 56, 57, 58, 59, 60, 61, 62,
			45, 46, 47, 48, 49, 50, 51, 52, 53,
			36, 37, 38, 39, 40, 41, 42, 43, 44,
			27, 28, 29, 30, 31, 32, 33, 34, 35,
			18, 19, 20, 21, 22, 23, 24, 25, 26,
			 9, 10, 11, 12, 13, 14, 15, 16, 17,
			 0,  1,  2,  3,  4,  5,  6,  7,  8
		],
		[
			89, 88, 87, 86, 85, 84, 83, 82, 81,
			80, 79, 78, 77, 76, 75, 74, 73, 72,
			71, 70, 69, 68, 67, 66, 65, 64, 63,
			62, 61, 60, 59, 58, 57, 56, 55, 54,
			53, 52, 51, 50, 49, 48, 47, 46, 45,
			44, 43, 42, 41, 40, 39, 38, 37, 36,
			35, 34, 33, 32, 31, 30, 29, 28, 27,
			26, 25, 24, 23, 22, 21, 20, 19, 18,
			17, 16, 15, 14, 13, 12, 11, 10,  9,
			 8,  7,  6,  5,  4,  3,  2,  1,  0
		]
	],

	// 已创建棋盘对象列表
	chessList: [],

	// 默认 Fen 串
	defaultFen: "rnbakabnr/9/1c5c1/p1p1p1p1p/9/9/P1P1P1P1P/1C5C1/9/RNBAKABNR w - - 0 1",

	// 空白 Fen 串
	blankFen: "9/9/9/9/9/9/9/9/9/9 w - - 0 1",

	// 棋谱信息项目列表
	info: {
		name: {
			title		: "棋局标题",
			event		: "赛事名称",
			red			: "红方名称",
			redteam		: "红方团体",
			redname		: "红方姓名",
			redeng		: "红方英文名",
			redlevel	: "红方等级",
			redrating	: "红方等级分",
			redtime		: "红方用时",
			black		: "黑方名称",
			blackteam	: "黑方团体",
			blackname	: "黑方姓名",
			blackeng	: "黑方英文名",
			blacklevel	: "黑方等级",
			blackrating	: "黑方等级分",
			blacktime	: "黑方用时",
			ecco		: "开局编号",
			open		: "布局类型",
			variation	: "变例类型",
			result		: "对局结果",
			remark		: "评注人员",
			author		: "棋谱作者",
			group		: "赛事组别",
			date		: "比赛日期",
			place		: "比赛地点",
			round		: "比赛轮次",
			table		: "比赛台次",
			judge		: "执台裁判",
			record		: "棋谱记录员"
		},
		pfc: {
			date		: "create-time"
		},
		DhtmlXQ: {},
		pgn: {
			place		: "Site",
			open		: "Opening",
			ecco		: "ECCO"
		}
	},
};

// 自身路径
vschess.selfPath = (function(){
	var currentElement = document.documentElement;

	while (currentElement.tagName.toLowerCase() !== "script") {
		currentElement = currentElement.lastChild;
	}

	return currentElement.src;
})();

// 默认路径为本程序的路径
vschess.defaultPath = vschess.selfPath.substring(0, vschess.selfPath.lastIndexOf("/") + 1);

// 涉及页面 DOM 的属性，单独抽出来
$.extend(vschess, {
	// Placeholder 支持情况
	placeholder: "placeholder" in document.createElement("input"),

	// 本地保存支持情况
	localDownload: !!window.Blob && !!window.URL && "download" in document.createElement("a"),

	// 标签列表
	tabList: "board move comment info export edit config".split(" "),

	// 钩子列表
	callbackList: "beforeClickAnimate afterClickAnimate loadFinish selectPiece unSelectPiece afterStartFen afterAnimate".split(" "),

	// 二进制棋谱扩展名列表
	binaryExt: "".split(" "),

	// 全局样式是否已加载完成的标记
	globalLoaded: false,

	// 全局样式加载完成后的回调
	globalLoadedCallback: [],

	// 声音列表
	soundList: "click bomb eat move check lose illegal".split(" "),

	// 音效组件缓存
	soundObject: {},

	// 风格音效是否已加载的标记，保证每个风格的音效只加载一次
	soundInit: {},

	// 风格样式是否已加载的标记，保证每个风格的样式只加载一次
	styleInit: {},

	// 风格样式是否已加载完成的标记
	styleLoaded: {},

	// 风格样式加载完成后的回调
	styleLoadedCallback: {},

	// 布局样式是否已加载的标记，保证每个布局的样式只加载一次
	layoutInit: {},

	// 布局样式是否已加载完成的标记
	layoutLoaded: {},

	// 布局样式加载完成后的回调
	layoutLoadedCallback: {},

	// 伪线程延时，20 为宜
	threadTimeout: 20,

	// 大棋谱生成东萍和鹏飞格式节点数临界点
	bigBookCritical: 10000,

	// 页面 Device Pixel Ratio
	dpr: window.devicePixelRatio || 1,

	// 编辑局面开始按钮列表
	editStartList: ["editStartButton", "editNodeStartButton", "editBeginButton", "editBlankButton", "editOpenButton", "editRandomReviewButton", "editRedOpeningButton", "editBlackOpeningButton"],

	// 编辑局面组件列表
	editModuleList: ["editEndButton", "editCancelButton", "editTips", "editTextarea", "editTextareaPlaceholder", "editPieceArea", "editBoard", "recommendClass", "recommendList", "editEditStartText", "editEditStartRound", "editEditStartPlayer"],

	// 粘贴棋谱组件列表
	editNodeModuleList: ["editNodeEndButton", "editNodeCancelButton", "editNodeTextarea", "editNodeTextareaPlaceholder"],

	// 状态参数语义化
	code: {
		// 棋子单击事件是否响应状态，0(0x00) 双方不响应，1(0x01) 仅黑方响应，2(0x10) 仅红方响应，3(0x11) 双方响应
		clickResponse: { none: 0, black: 1, red: 2, both: 3 },

		// 棋盘方向，0(0x00) 不翻转，1(0x01) 左右翻转，2(0x10) 上下，3(0x11) 对角旋转（左右+上下）
		turn: { none: 0, mirror: 1, reverse: 2, round: 3 }
	},

	// 可自动识别的棋谱信息项目列表
	autoInfo: "ecco open variation result".split(" "),

    // 可导出棋谱格式列表
    exportFormatList: {
        DhtmlXQ: "东萍 DhtmlXQ UBB 格式",
        ChessDB: "云库指令格式",
        Text: "文本 TXT 格式",
        TextBoard: "文字棋盘"
    },
});

// 程序默认参数
vschess.defaultOptions = {
	// 中文着法文字
	ChineseChar: {
		Piece	 : "车马相仕帅炮兵车马象士将炮卒",
		Number	 : "一二三四五六七八九１２３４５６７８９",
		PawnIndex: "一二三四五一二三四五",
		Text	 : "前中后进退平"
	}
};

// 涉及页面 DOM 的默认参数，单独抽出来
$.extend(vschess.defaultOptions, {
	// 选择解析器，默认为自动选择
	parseType: "auto",

	// 自定义棋谱
	chessData: false,

	// 默认风格
	style: "default",

	// 默认布局
	layout: "default",

	// 默认全局样式
	globalCSS: vschess.defaultPath + "global.css",

	// 默认棋盘初始化时展示的局面索引
	currentStep: 0,

	// 音效开关
	sound: true,

	// 默认音效
	soundStyle: "default",

	// 默认音量
	volume: 100,

	// 自定义音效路径，空字符串表示程序自动识别，如需自定义请参考官方文档
	soundPath: "",

	// 着法朗读
	speakMove: false,

	// IE6 自定义棋子图片路径，如需自定义请参考官方文档
	IE6Compatible_CustomPieceUrl: false,

	// 默认棋盘方向，0(0x00) 不翻转，1(0x01) 左右翻转，2(0x10) 上下翻转，3(0x11) 对角旋转
	// 亦可以使用 vschess.code.turn：none 不翻转，mirror 左右翻转，reverse 上下翻转，round 对角旋转
	turn: vschess.code.turn.none,

	// 默认棋子单击事件是否响应状态，0(0x00) 双方不响应，1(0x01) 仅黑方响应，2(0x10) 仅红方响应，3(0x11) 双方响应
	// 亦可以使用 vschess.code.clickResponse：none 双方不响应，black 仅黑方响应，red 仅红方响应，both 双方响应
	clickResponse: vschess.code.clickResponse.both,

	// 默认走子动画时间，单位毫秒
	animationTime: 200,

	// 默认播放间隔时间，单位百毫秒（0.1秒）
	playGap: 5,

	// 默认着法格式
	moveFormat: "chinese",

	// 单击事件名称，兼顾 PC 端和移动端
	click: (function(){
		var UA = navigator.userAgent.toLowerCase(), click = "touchend";
		!~UA.indexOf("android") && !~UA.indexOf("iph") && !~UA.indexOf("ipad") && (click = "click");
		return click;
	})(),

	// 快进快退局面数
	quickStepOffset: 10,

	// 默认展开的标签
	defaultTab: "comment",

	// UBB 分享标签名称
	ubbTagName: "vschess",

	// 走子提示
	moveTips: true,

	// 保存提示
	saveTips: false,

	// 棋子随机旋转
	pieceRotate: false,

	// 禁止重复长打
	banRepeatLongThreat: true,

	// 禁止重复一将一杀
	banRepeatLongKill: false,

	// 违例提示
	illegalTips: true,

	// 起始局面提示信息
	startTips: [
		"蓝色的着法含有变着",
		"标有星号的着法含有注解",
		"支持东萍、鹏飞等多种格式",
		"单击“复制”复制当前局面",
		'<a href="https://www.xiaxiangqi.com/vschess/" target="_blank">微思象棋播放器 V' + vschess.version + "</a>",
		'<a href="https://margin.top/" target="_blank">Margin.Top &copy; 版权所有</a>'
	],

	// 云服务 API 地址
	cloudApi: {
		startFen: "https://www.xiaxiangqi.com/api/cloud/startfen",
		saveBook: "https://www.xiaxiangqi.com/api/cloud/savebook",
	},

	// 默认推荐起始局面列表
	recommendList: [
		{ name: "常用开局", fenList: [
			{ name: "空白棋盘", fen: "9/9/9/9/9/9/9/9/9/9 w - - 0 1" },
			{ name: "只有帅将", fen: "5k3/9/9/9/9/9/9/9/9/3K5 w - - 0 1" },
			{ name: "标准开局", fen: "rnbakabnr/9/1c5c1/p1p1p1p1p/9/9/P1P1P1P1P/1C5C1/9/RNBAKABNR w - - 0 1" },
			{ name: "红让左马", fen: "rnbakabnr/9/1c5c1/p1p1p1p1p/9/9/P1P1P1P1P/1C5C1/9/R1BAKABNR w - - 0 1" },
			{ name: "黑让左马", fen: "rnbakab1r/9/1c5c1/p1p1p1p1p/9/9/P1P1P1P1P/1C5C1/9/RNBAKABNR w - - 0 1" },
			{ name: "红让右马", fen: "rnbakabnr/9/1c5c1/p1p1p1p1p/9/9/P1P1P1P1P/1C5C1/9/RNBAKAB1R w - - 0 1" },
			{ name: "黑让右马", fen: "r1bakabnr/9/1c5c1/p1p1p1p1p/9/9/P1P1P1P1P/1C5C1/9/RNBAKABNR w - - 0 1" },
			{ name: "红让双马", fen: "rnbakabnr/9/1c5c1/p1p1p1p1p/9/9/P1P1P1P1P/1C5C1/9/R1BAKAB1R w - - 0 1" },
			{ name: "黑让双马", fen: "r1bakab1r/9/1c5c1/p1p1p1p1p/9/9/P1P1P1P1P/1C5C1/9/RNBAKABNR w - - 0 1" },
			{ name: "红让双仕", fen: "rnbakabnr/9/1c5c1/p1p1p1p1p/9/9/P1P1P1P1P/1C5C1/9/RNB1K1BNR w - - 0 1" },
			{ name: "黑让双士", fen: "rnb1k1bnr/9/1c5c1/p1p1p1p1p/9/9/P1P1P1P1P/1C5C1/9/RNBAKABNR w - - 0 1" },
			{ name: "红让双相", fen: "rnbakabnr/9/1c5c1/p1p1p1p1p/9/9/P1P1P1P1P/1C5C1/9/RN1AKA1NR w - - 0 1" },
			{ name: "黑让双象", fen: "rn1aka1nr/9/1c5c1/p1p1p1p1p/9/9/P1P1P1P1P/1C5C1/9/RNBAKABNR w - - 0 1" },
			{ name: "红让仕相", fen: "rnbakabnr/9/1c5c1/p1p1p1p1p/9/9/P1P1P1P1P/1C5C1/9/RN2K2NR w - - 0 1" },
			{ name: "黑让士象", fen: "rn2k2nr/9/1c5c1/p1p1p1p1p/9/9/P1P1P1P1P/1C5C1/9/RNBAKABNR w - - 0 1" },
			{ name: "红让五兵", fen: "rnbakabnr/9/1c5c1/p1p1p1p1p/9/9/9/1C5C1/9/RNBAKABNR w - - 0 1" },
			{ name: "黑让五卒", fen: "rnbakabnr/9/1c5c1/9/9/9/P1P1P1P1P/1C5C1/9/RNBAKABNR w - - 0 1" },
			{ name: "红让九子", fen: "rnbakabnr/9/1c5c1/p1p1p1p1p/9/9/9/1C5C1/9/RN2K2NR w - - 0 1" },
			{ name: "黑让九子", fen: "rn2k2nr/9/1c5c1/9/9/9/P1P1P1P1P/1C5C1/9/RNBAKABNR w - - 0 1" }
		]}
    ],

    // 标签名称
    tagName: {
        comment: "棋谱注解",
        info: "棋局信息",
        export: "棋谱导出",
        edit: "棋谱导入",
        config: "棋盘选项"
    }
});

// 默认帮助信息
vschess.defaultOptions.help  = '<h1>微思象棋播放器 V' + vschess.version + ' 帮助信息</h1>';
vschess.defaultOptions.help += '<hr />';
vschess.defaultOptions.help += '<h2>1.&ensp;&ensp;单击“播放”按钮，可以自动播放棋局；播放过程中，单击“暂停”按钮，棋局停止自动播放。</h2>';
vschess.defaultOptions.help += '<h2>2.&ensp;&ensp;单击“前进”、“后退”按钮，每次变化1步；单击“快进”、“快退”按钮，每次变化#quickStepOffsetRound#个回合，即#quickStepOffset#步。</h2>';
vschess.defaultOptions.help += '<h2>3.&ensp;&ensp;单击“复制”按钮，可以复制当前局面。</h2>';
vschess.defaultOptions.help += '<h2>4.&ensp;&ensp;复制局面后，可以直接在专业象棋软件中粘贴使用。</h2>';
vschess.defaultOptions.help += '<h2>5.&ensp;&ensp;分析局面时，建议将局面复制到专业象棋软件中进行分析。</h2>';
vschess.defaultOptions.help += '<h2>6.&ensp;&ensp;可以直接在棋盘上走棋，便于分析局面。</h2>';
vschess.defaultOptions.help += '<h2>7.&ensp;&ensp;在着法列表中可以调整变招顺序或删除着法。</h2>';
vschess.defaultOptions.help += '<h2>8.&ensp;&ensp;注释修改后直接在注释区外面任意处单击即可生效。</h2>';
vschess.defaultOptions.help += '<h2>9.&ensp;&ensp;编辑局面会失去当前棋谱，请注意保存。</h2>';
vschess.defaultOptions.help += '<h2>10.&ensp;编辑局面标签中，可以直接打开电脑中的棋谱，也可以直接将棋谱文件拖拽到本棋盘上。</h2>';
vschess.defaultOptions.help += '<h2>11.&ensp;支持东萍、鹏飞、象棋世家、标准PGN、中国游戏中心、QQ象棋等格式，其他格式程序也会尝试自动识别。</h2>';
vschess.defaultOptions.help += '<h2>12.&ensp;棋盘选项中，可以控制棋盘方向、播放速度、走子声音等。</h2>';
vschess.defaultOptions.help += '<h2>13.&ensp;棋谱分享功能生成的论坛 UBB 代码，可以在支持该代码的论坛中使用。<a href="https://www.xiaxiangqi.com/" target="_blank">【查看都有哪些论坛支持该代码】</a></h2>';
vschess.defaultOptions.help += '<hr />';
vschess.defaultOptions.help += '<h2><a href="https://www.xiaxiangqi.com/vschess/" target="_blank">微思象棋播放器 V' + vschess.version + '</a> <a href="https://margin.top/" target="_blank">Margin.Top &copy; 版权所有</a></h2>';

// IE6 兼容，棋子 PNG 图片透明，如果需要自定义棋子图片路径，请参考官方文档
vschess.IE6Compatible_setPieceTransparent = function(options){
	if (!window.ActiveXObject || window.XMLHttpRequest || options.IE6Compatible_CustomPieceUrl) {
		return this;
	}

	var cssRule = 'filter: progid:DXImageTransform.Microsoft.AlphaImageLoader(enabled="true", sizingMethod="scale", src="#"); background:none;';
	var sheet = document.createStyleSheet();

	sheet.addRule(".vschess-style-" + options.style + " .vschess-piece-S"     , cssRule.replace("#", vschess.defaultPath + 'style/' + options.style + "/nr.png"));
	sheet.addRule(".vschess-style-" + options.style + " .vschess-piece-s"     , cssRule.replace("#", vschess.defaultPath + 'style/' + options.style + "/ns.png"));
	sheet.addRule(".vschess-style-" + options.style + " .vschess-piece-R span", cssRule.replace("#", vschess.defaultPath + 'style/' + options.style + "/rr.png"));
	sheet.addRule(".vschess-style-" + options.style + " .vschess-piece-N span", cssRule.replace("#", vschess.defaultPath + 'style/' + options.style + "/rn.png"));
	sheet.addRule(".vschess-style-" + options.style + " .vschess-piece-B span", cssRule.replace("#", vschess.defaultPath + 'style/' + options.style + "/rb.png"));
	sheet.addRule(".vschess-style-" + options.style + " .vschess-piece-A span", cssRule.replace("#", vschess.defaultPath + 'style/' + options.style + "/ra.png"));
	sheet.addRule(".vschess-style-" + options.style + " .vschess-piece-K span", cssRule.replace("#", vschess.defaultPath + 'style/' + options.style + "/rk.png"));
	sheet.addRule(".vschess-style-" + options.style + " .vschess-piece-C span", cssRule.replace("#", vschess.defaultPath + 'style/' + options.style + "/rc.png"));
	sheet.addRule(".vschess-style-" + options.style + " .vschess-piece-P span", cssRule.replace("#", vschess.defaultPath + 'style/' + options.style + "/rp.png"));
	sheet.addRule(".vschess-style-" + options.style + " .vschess-piece-r span", cssRule.replace("#", vschess.defaultPath + 'style/' + options.style + "/br.png"));
	sheet.addRule(".vschess-style-" + options.style + " .vschess-piece-n span", cssRule.replace("#", vschess.defaultPath + 'style/' + options.style + "/bn.png"));
	sheet.addRule(".vschess-style-" + options.style + " .vschess-piece-b span", cssRule.replace("#", vschess.defaultPath + 'style/' + options.style + "/bb.png"));
	sheet.addRule(".vschess-style-" + options.style + " .vschess-piece-a span", cssRule.replace("#", vschess.defaultPath + 'style/' + options.style + "/ba.png"));
	sheet.addRule(".vschess-style-" + options.style + " .vschess-piece-k span", cssRule.replace("#", vschess.defaultPath + 'style/' + options.style + "/bk.png"));
	sheet.addRule(".vschess-style-" + options.style + " .vschess-piece-c span", cssRule.replace("#", vschess.defaultPath + 'style/' + options.style + "/bc.png"));
	sheet.addRule(".vschess-style-" + options.style + " .vschess-piece-p span", cssRule.replace("#", vschess.defaultPath + 'style/' + options.style + "/bp.png"));

	return this;
};

// 从二进制原始数据中抽取棋局信息
vschess.binaryToInfo = function(buffer, parseType){
    parseType = parseType || "auto";

    // 未能识别的数据，返回空
	return {};
};


// 将二进制原始数据转换为棋谱节点树，这里的变招都是节点，变招的切换即为默认节点的切换
vschess.binaryToNode = function(buffer, parseType){
    parseType = parseType || "auto";

    // 未能识别的数据，返回起始局面
	return { fen: vschess.defaultFen, comment: "", next: [], defaultIndex: 0 };
};


// 从原始数据中抽取棋局信息
vschess.dataToInfo = function(chessData, parseType){
	chessData = vschess.replaceNbsp(chessData);
	var replaceQuote = chessData.replace(/\'/g, '"');
	parseType = parseType || "auto";

	// 东萍象棋 DhtmlXQ 格式
	if (parseType === "auto" && ~replaceQuote.indexOf("[DhtmlXQ") || parseType === "DhtmlXQ") {
		return vschess.dataToInfo_DhtmlXQ(chessData);
	}

	// 未能识别的数据，返回空
	return {};
};

// 从东萍象棋 DhtmlXQ 格式中抽取棋局信息
vschess.dataToInfo_DhtmlXQ = function(chessData){
	var eachLine = chessData.split("[DhtmlXQ");
	var small = [];

	for (var i = 0; i < eachLine.length; ++i) {
		~eachLine[i].indexOf("_comment") || ~eachLine[i].indexOf("_move") || small.push(eachLine[i]);
	}

	chessData = small.join("[DhtmlXQ");
	var result = {};

	for (var i in vschess.info.name) {
		var startTag = "[DhtmlXQ_" + (vschess.info.DhtmlXQ[i] || i) + "]";
		var startPos = chessData.indexOf(startTag);

		if (~startPos) {
			var value = chessData.substring(startPos + startTag.length, chessData.indexOf("[/DhtmlXQ_", startPos));
			value && (result[i] = vschess.stripTags(value));
		}
	}

	result.result = vschess.dataText(result.result, "result");
	return result;
};

// 将原始数据转换为棋谱节点树，这里的变招都是节点，变招的切换即为默认节点的切换
vschess.dataToNode = function(chessData, parseType){
	var match, RegExp = vschess.RegExp();
	parseType = parseType || "auto";

	// 东萍象棋 DhtmlXQ 格式
	if (parseType === "auto" && ~chessData.indexOf("[DhtmlXQ") || parseType === "DhtmlXQ") {
		return vschess.dataToNode_DhtmlXQ(chessData);
	}

	// 长 Fen 串
	if (match = RegExp.FenLong.exec(chessData)) {
		return { fen: match[0], comment: "", next: [], defaultIndex: 0 };
	}

	// 短 Fen 串
	if (match = RegExp.FenShort.exec(chessData)) {
		return { fen: match[0] + " - - 0 1", comment: "", next: [], defaultIndex: 0 };
	}

	// 迷你 Fen 串
	if (match = RegExp.FenMini.exec(chessData)) {
		return { fen: match[0] + " w - - 0 1", comment: "", next: [], defaultIndex: 0 };
	}

	// 未能识别的数据，返回起始局面
	return { fen: vschess.defaultFen, comment: "", next: [], defaultIndex: 0 };
};


// 将东萍象棋 DhtmlXQ 格式转换为棋谱节点树
vschess.dataToNode_DhtmlXQ = function(chessData, onlyFen){
	var DhtmlXQ_Comment	 = {};
	var DhtmlXQ_Change	 = [];
	var DhtmlXQ_Start	 = "";
	var DhtmlXQ_MoveList = "";
	var DhtmlXQ_Fen		 = "";
	var DhtmlXQ_EachLine = chessData.split("[DhtmlXQ");

	for (var i = 0; i < DhtmlXQ_EachLine.length; ++i) {
		var l = "[DhtmlXQ" + DhtmlXQ_EachLine[i];

		if (~l.indexOf("[DhtmlXQ_comment")) {
			var start	  = l.indexOf("]");
			var commentId = l.substring(16, start);
			~commentId.indexOf("_") || (commentId = "0_" + commentId);
			DhtmlXQ_Comment[commentId] = l.substring(start + 1, l.indexOf("[/DhtmlXQ_")).replace(/\|\|/g, "\n").replace(/\\u([0-9a-zA-Z]{4})/g, function(){ return vschess.fcc(parseInt(arguments[1], 16)); });
		}
		else if (~l.indexOf("[DhtmlXQ_binit")) {
			DhtmlXQ_Start = l.substring(l.indexOf("[DhtmlXQ_binit") + 15, l.indexOf("[/DhtmlXQ_"));
		}
		else if (~l.indexOf("[DhtmlXQ_movelist")) {
			DhtmlXQ_MoveList = l.substring(l.indexOf("[DhtmlXQ_movelist") + 18, l.indexOf("[/DhtmlXQ_"));
		}
		else if (~l.indexOf("[DhtmlXQ_move_")) {
			var start	 = l.indexOf("]");
			var changeId = l.substring(14, start);
			DhtmlXQ_Change.push({ id: changeId, change: l.substring(start + 1, l.indexOf("[/DhtmlXQ_")) });
		}
		else if (~l.indexOf("[DhtmlXQ_fen")) {
			DhtmlXQ_Fen = l.substring(l.indexOf("[DhtmlXQ_fen") + 13, l.indexOf("[/DhtmlXQ_"));
		}
	}

	// Fen 串优先
	if (DhtmlXQ_Fen) {
		var DhtmlXQ_ToFenFinal = DhtmlXQ_Fen;
	}
	// 抽取起始局面，生成起始 Fen 串
	else {
		if (DhtmlXQ_Start) {
			var DhtmlXQ_ToFen = new Array(91).join("*").split(""), DhtmlXQ_ToFenFinal = [];
			var DhtmlXQ_ToFenPiece = "RNBAKABNRCCPPPPPrnbakabnrccppppp";

			for (var i = 0; i < 32; ++i) {
				var move = DhtmlXQ_Start.substring(i * 2, i * 2 + 2).split("");
				DhtmlXQ_ToFen[+move[0] + move[1] * 9] = DhtmlXQ_ToFenPiece.charAt(i);
			}

			DhtmlXQ_ToFenFinal = vschess.arrayToFen(DhtmlXQ_ToFen);
		}
		else {
			var DhtmlXQ_ToFenFinal = vschess.defaultFen.split(" ")[0];
			var DhtmlXQ_ToFen = vschess.fenToArray(DhtmlXQ_ToFenFinal);
		}

		if (DhtmlXQ_MoveList) {
			var firstMovePos = DhtmlXQ_MoveList.substring(0, 2).split("");
			DhtmlXQ_ToFenFinal += vschess.cca(DhtmlXQ_ToFen[+firstMovePos[0] + firstMovePos[1] * 9]) > 96 ? " b - - 0 1" : " w - - 0 1";
		}
		else {
			var checkW = DhtmlXQ_ToFenFinal + " w - - 0 1";
			var checkB = DhtmlXQ_ToFenFinal + " b - - 0 1";
			DhtmlXQ_ToFenFinal = vschess.checkFen(checkB).length < vschess.checkFen(checkW).length ? checkB : checkW;
		}
	}

	if (onlyFen) {
		return DhtmlXQ_ToFenFinal;
	}

	var branchHashTable = {};

	// DhtmlXQ 着法列表转换为 node 节点列表
	function DhtmlXQ_MoveToMove(s){
		var moveList = [];

		while (s.length) {
			var move = s.slice(-4).split("");
			moveList.push(vschess.fcc(+move[0] + 97) + (9 - move[1]) + vschess.fcc(+move[2] + 97) + (9 - move[3]));
			s = s.slice(0, -4);
		}

		return moveList;
	}

	// 根据 node 节点列表创建分支
	function makeBranch(list, target, b, i){
		var next = { move: list.pop(), comment: DhtmlXQ_Comment[b + "_" + i] || "", next: [], defaultIndex: 0 };
		branchHashTable[b + "_" + ++i] = next;
		target.next.push(next);
		list.length && makeBranch(list, next, b, i);
	}

	// 生成主分支
	var result   = { fen: DhtmlXQ_ToFenFinal, comment: DhtmlXQ_Comment["0_0"] || "", next: [], defaultIndex: 0 };
	var moveList = DhtmlXQ_MoveToMove(DhtmlXQ_MoveList);
	branchHashTable["0_1"] = result;
	moveList.length && makeBranch(moveList, result, 0, 1);

	// 生成变着分支
	var undoList = [];

	for (var i = 0; i < DhtmlXQ_Change.length; ++i) {
		var line   = DhtmlXQ_Change[i];
		var id     = line.id.split("_");
		var target = branchHashTable[id[0] + "_" + id[1]];

		if (target) {
			var moveList = DhtmlXQ_MoveToMove(line.change);
			moveList.length && makeBranch(moveList, target, id[2], id[1]);
			undoList.length = 0;
		}
		else {
			if (~undoList.indexOf(line.id)) {
				break;
			}
			else {
				DhtmlXQ_Change.push(line   );
				undoList      .push(line.id);
			}
		}
	}

	return result;
};



// 将着法列表转换为棋谱节点树
vschess.stepListToNode = function(fen, stepList){
	function makeBranch(list, target, b, i){
		var step = list.shift();
		var next = { move: step, comment: "", next: [], defaultIndex: 0 };
		target.next.push(next);
		list.length && makeBranch(list, next, b, i + 1);
	}

	var result = { fen: fen || vschess.defaultFen, comment: "", next: [], defaultIndex: 0 };
	stepList.length && makeBranch(stepList, result, 0, 1);
	return result;
};

// 将整数限制在一个特定的范围内
vschess.limit = function(num, min, max, defaultValue){
	typeof num === "undefined" && typeof defaultValue !== "undefined" && (num = defaultValue);
	vschess.isNumber(min) || (min = -Infinity);
	vschess.isNumber(max) || (max =  Infinity);
	vschess.isNumber(num) || (num =         0);
	num < min && (num = min);
	num > max && (num = max);
	return +num;
};

// 正则表达式，使用时都是新的，避免出现 lastIndex 冲突
vschess.RegExp = function(){
	return {
		// Fen 串识别正则表达式
		FenLong	: /(?:[RNHBEAKCPrnhbeakcp1-9]{1,9}\/){9}[RNHBEAKCPrnhbeakcp1-9]{1,9}[\s][wbr][\s]-[\s]-[\s][0-9]+[\s][0-9]+/,
		FenShort: /(?:[RNHBEAKCPrnhbeakcp1-9]{1,9}\/){9}[RNHBEAKCPrnhbeakcp1-9]{1,9}[\s][wbr]/,
		FenMini : /(?:[RNHBEAKCPrnhbeakcp1-9]{1,9}\/){9}[RNHBEAKCPrnhbeakcp1-9]{1,9}/,

		// 通用棋步识别正则表达式
		Chinese	: /[\u8f66\u8eca\u4fe5\u9a6c\u99ac\u508c\u76f8\u8c61\u4ed5\u58eb\u5e05\u5e25\u5c06\u5c07\u70ae\u5305\u7832\u5175\u5352\u524d\u4e2d\u540e\u5f8c\u4e00\u4e8c\u4e09\u56db\u4e94\u58f9\u8d30\u53c1\u8086\u4f0d\uff11\uff12\uff13\uff14\uff151-5][\u8f66\u8eca\u4fe5\u9a6c\u99ac\u508c\u76f8\u8c61\u4ed5\u58eb\u70ae\u5305\u7832\u5175\u5352\u4e00\u4e8c\u4e09\u56db\u4e94\u516d\u4e03\u516b\u4e5d\u58f9\u8d30\u53c1\u8086\u4f0d\u9646\u67d2\u634c\u7396\uff11\uff12\uff13\uff14\uff15\uff16\uff17\uff18\uff191-9][\u8fdb\u9032\u9000\u5e73][\u4e00\u4e8c\u4e09\u56db\u4e94\u516d\u4e03\u516b\u4e5d\u58f9\u8d30\u53c1\u8086\u4f0d\u9646\u67d2\u634c\u7396\uff11\uff12\uff13\uff14\uff15\uff16\uff17\uff18\uff191-9]/g,
		Node	: /[A-Ia-i][0-9][A-Ia-i][0-9]/g,

		// 特殊兵东萍表示法
		Pawn	: /[\+\-2][1-9][\+\-\.][1-9]/
	};
};

// Fen 串是否为红方
vschess.fenIsR = function(fen){
	return !vschess.fenIsB(fen);
};

// Fen 串是否为黑方
vschess.fenIsB = function(fen){
	return fen.split(" ")[1].toLowerCase() === "b";
};

// Fen 串改变走棋方
vschess.fenChangePlayer = function(fen){
	var RegExp = vschess.RegExp();
	RegExp.FenShort.test(fen) || (fen = vschess.defaultFen);
	var fenSplit = fen.split(" ");
	fenSplit[1]  = vschess.fenIsB(fen) ? "w" : "b";
	return fenSplit.join(" ");
};

// Fen 串转换为局面
vschess.fenToSituation = function(fen){
	var fenSplit  = fen.split(" ");
	var situation = vschess.situation.slice(0);
	var currentPiece = 0;
	var pieceEach = vschess.fenToArray(fen);
	situation[0] = vschess.fenIsB(fen) ? 2 : 1;
	situation[1] = vschess.limit(fenSplit[5], 1, Infinity);

	for (var i = 51; i < 204; ++i) {
		situation[i] && (situation[i] = vschess.f2n[pieceEach[currentPiece++]]);
	}

	return situation;
};

// 局面转换为 Fen 串
vschess.situationToFen = function(situation){
	var fen = [];

	for (var i = 51; i < 204; ++i) {
		situation[i] && fen.push(vschess.n2f[situation[i]]);
	}

	fen = vschess.arrayToFen(fen);
	return fen + (situation[0] === 1 ? " w - - 0 " : " b - - 0 ") + situation[1];
};

// 翻转 FEN 串
vschess.turnFen = function(fen){
	var RegExp = vschess.RegExp();
	RegExp.FenShort.test(fen) || (fen = vschess.defaultFen);
	var fenSplit = fen        .split(" ");
	var lines    = fenSplit[0].split("/");

	for (var i = 0; i < 10; ++i) {
		lines[i] = lines[i].split("").reverse().join("");
	}

	fenSplit[0] = lines.join("/");
	fenSplit.length <= 2 && (fenSplit.push("- - 0 1"));
	return fenSplit.join(" ");
};

// 旋转 FEN 串
vschess.roundFen = function(fen){
	var RegExp = vschess.RegExp();
	RegExp.FenShort.test(fen) || (fen = vschess.defaultFen);
	var fenSplit = fen        .split(" ");
	fenSplit[0]  = fenSplit[0].split("").reverse().join("");
	fenSplit.length <= 2 && (fenSplit.push("- - 0 1"));
	return fenSplit.join(" ");
};

// 翻转节点 ICCS 着法
vschess.turnMove = function(move){
	move = move.split("");
	move[0] = vschess.fcc(202 - vschess.cca(move[0]));
	move[2] = vschess.fcc(202 - vschess.cca(move[2]));
	return move.join("");
};

// 旋转节点 ICCS 着法
vschess.roundMove = function(move){
	move = move.split("");
	move[0] = vschess.fcc(202 - vschess.cca(move[0]));
	move[2] = vschess.fcc(202 - vschess.cca(move[2]));
	move[1] = 9 - move[1];
	move[3] = 9 - move[3];
	return move.join("");
};

// 翻转 WXF 着法，不可用于特殊兵
vschess.turnWXF = function(oldMove){
	// isMBA: is Middle Before After
	var moveSplit = oldMove.split(""), isMBA = ~"+-.".indexOf(moveSplit[1]);

	// NBA: 不是你想象中的 NBA，而是马相仕（马象士）
	if (~"NBA".indexOf(moveSplit[0]) || moveSplit[2] === ".") {
		if (isMBA) {
			return oldMove.substring(0, 3) + (10 - moveSplit[3]);
		}

		return moveSplit[0] + (10 - moveSplit[1]) + moveSplit[2] + (10 - moveSplit[3]);
	}

	if (isMBA) {
		return oldMove;
	}

	return moveSplit[0] + (10 - moveSplit[1]) + oldMove.substring(2, 4);
};

// 统计局面中棋子数量
vschess.countPieceLength = function(situation){
	if (typeof situation === "string") {
		var RegExp = vschess.RegExp();
		RegExp.FenShort.test(situation) && (situation = vschess.fenToSituation(situation));
	}

	for (var i = 51, count = 0; i < 204; ++i) {
		situation[i] > 1 && ++count;
	}

	return count;
};


// Fen 串移动一枚棋子
vschess.fenMovePiece = function(fen, move){
	var RegExp = vschess.RegExp();
	RegExp.FenShort.test(fen) || (fen = vschess.defaultFen);
	var situation = vschess.fenToSituation(fen);
	var src = vschess.i2s[move.substring(0, 2)];
	var dst = vschess.i2s[move.substring(2, 4)];
	situation[dst] = situation[src];
	situation[src] = 1;
	situation[0]   = 3    - situation[0];
	situation[0] === 1 && ++situation[1];
	return vschess.situationToFen(situation);
};

// Fen 串颠倒红黑
vschess.invertFen = function(fen){
	var RegExp = vschess.RegExp();
	RegExp.FenShort.test(fen) || (fen = vschess.defaultFen);
	var fenSplit = fen.split(" ");
	fenSplit[1]  = vschess.fenIsB(fen) ? "w" : "b";
	fenSplit.length <= 2 && (fenSplit.push("- - 0 1"));
	var eachPiece = fenSplit[0].split("");

	for (var i = 0; i < eachPiece.length; ++i) {
		eachPiece[i] = vschess.cca(eachPiece[i]) > 96 ? eachPiece[i].toUpperCase() : eachPiece[i].toLowerCase();
	}

	fenSplit[0] = eachPiece.join("");
	return fenSplit.join(" ");
};

// 获取棋局信息显示文本
vschess.showText = function(showText, item){
	var map = {
		result: { "*": "", "1-0": "红胜", "0-1": "黑胜", "1/2-1/2": "和棋" }
	};

	return map[item] && map[item][showText] || showText;
};

// 获取棋局信息数据文本
vschess.dataText = function(dataText, item){
	var map = {
		result: {
			"红胜": "1-0", "红先胜": "1-0", "黑负": "1-0",
			"红负": "0-1", "红先负": "0-1", "黑胜": "0-1", "0-1": "0-1",
			"红和": "1/2-1/2", "红先和": "1/2-1/2", "和棋": "1/2-1/2", "和": "1/2-1/2",
			"1-0": "1-0", "0-1": "0-1", "1/2-1/2": "1/2-1/2",
			__default__: "*"
		}
	};

	return map[item] && (map[item][dataText] || map[item].__default__) || dataText;
};

// PGN 字段驼峰化
vschess.fieldNameToCamel = function(fieldName){
	var key = fieldName || "";
	var keySplit = key.split("");

	if (key.length > 3 && key.substring(0, 3) === "red") {
		keySplit[0] = "R";
		keySplit[3] = keySplit[3].toUpperCase();
	}
	else if (key.length > 5 && key.substring(0, 5) === "black") {
		keySplit[0] = "B";
		keySplit[5] = keySplit[5].toUpperCase();
	}
	else {
		keySplit[0] = keySplit[0].toUpperCase();
	}

	return keySplit.join("");
};

// GUID 生成器
vschess.guid = function(){
	var guid = "";

	for (var i = 0; i < 32; ++i) {
		guid += Math.floor(Math.random() * 16).toString(16);
		~[7, 11, 15, 19].indexOf(i) && (guid += "-");
	}

	return guid;
};

// String.fromCharCode 别名
vschess.fcc = function(code){
	return String.fromCharCode(code);
};

// String.charCodeAt 别名
vschess.cca = function(word){
	return word.charCodeAt(0);
};

// 左右填充
vschess.strpad = function(str, length, pad, direction){
	str = str || "" ; str += "";
	pad = pad || " "; pad += "";
	length = vschess.limit(length, 0, Infinity, 0);

	if (length > str.length) {
		if (direction === "left" || direction === "l") {
			return new Array(length - str.length + 1).join(pad) + str;
		}
		else if (direction === "right" || direction === "r") {
			return str + new Array(length - str.length + 1).join(pad);
		}
		else {
			return new Array(Math.floor((length - str.length) / 2) + 1).join(pad) + str + new Array(Math.ceil((length - str.length) / 2) + 1).join(pad);
		}
	}
	else {
		return str;
	}
};

// 判断字符串是否为数字
vschess.isNumber = function(str){
	return !isNaN(+str);
};

// 拆分 Fen 串
vschess.fenToArray = function(fen){
	return fen.split(" ")[0]
		.replace(/H/g, "N")
		.replace(/E/g, "B")
		.replace(/h/g, "n")
		.replace(/e/g, "b")
		.replace(/1/g, "*")
		.replace(/2/g, "**")
		.replace(/3/g, "***")
		.replace(/4/g, "****")
		.replace(/5/g, "*****")
		.replace(/6/g, "******")
		.replace(/7/g, "*******")
		.replace(/8/g, "********")
		.replace(/9/g, "*********")
		.replace(/\//g,"").split("");
};

// 合并 Fen 串
vschess.arrayToFen = function(array){
	var tempArr = [], blank = 0;

	for (var i = 0; i < 90; ++i) {
		if (array[i] === "*") {
			++blank;
		}
		else {
			blank && tempArr.push(blank);
			blank = 0;
			tempArr.push(array[i]);
		}

		if (i % 9 === 8) {
			blank && tempArr.push(blank);
			blank = 0;
			tempArr.push("/");
		}
	}

	--tempArr.length;
	return tempArr.join("");
};

// 取得指定弧度值旋转 CSS 样式
vschess.degToRotateCSS = function(deg){
	if (window.ActiveXObject) {
		var css = "filter:progid:DXImageTransform.Microsoft.Matrix(SizingMethod=sMethod,M11=#M11,M12=#M12,M21=#M21,M22=#M22)";
		var rad =  Math.PI * deg / 180;
		var M11 =  Math.cos(deg);
		var M12 = -Math.sin(deg);
		var M21 =  Math.sin(deg);
		var M22 =  Math.cos(deg);
		return css.replace("#M11", M11).replace("#M12", M12).replace("#M21", M21).replace("#M22", M22);
	}
	else {
		var css = "";
		css +=         "transform:rotate(" + deg + "deg);";
		css +=      "-o-transform:rotate(" + deg + "deg);";
		css +=     "-ms-transform:rotate(" + deg + "deg);";
		css +=    "-moz-transform:rotate(" + deg + "deg);";
		css += "-webkit-transform:rotate(" + deg + "deg);";
		return css;
	}
};

// 文字棋盘
vschess.textBoard = function(fen, options) {
	var RegExp = vschess.RegExp();
	RegExp.FenShort.test(fen) || (fen = vschess.defaultFen);
	typeof options === "undefined" && (options = vschess.defaultOptions);

	function piece(f){
		var pieceId = vschess.f2n[f];

		if (pieceId > 32) {
			return "[" + options.ChineseChar.Piece[(pieceId & 15) + 6] + "]";
		}

		if (pieceId > 16) {
			return "(" + options.ChineseChar.Piece[(pieceId & 15) - 1] + ")";
		}

		return "----";
	}

	var isB = vschess.fenIsB(fen);
	var board = vschess.fenToArray(fen);
	var text = [isB ? "黑方 走棋方\n\n" : "黑方\n\n"];

	var boardText = [
		" ┌-", "-┬-", "-┬-", "-┬-", "-┬-", "-┬-", "-┬-", "-┬-", "-┐ ",
		" ├-", "-┼-", "-┼-", "-┼-", "-※-", "-┼-", "-┼-", "-┼-", "-┤ ",
		" ├-", "-┼-", "-┼-", "-┼-", "-┼-", "-┼-", "-┼-", "-┼-", "-┤ ",
		" ├-", "-┼-", "-┼-", "-┼-", "-┼-", "-┼-", "-┼-", "-┼-", "-┤ ",
		" ├-", "-┴-", "-┴-", "-┴-", "-┴-", "-┴-", "-┴-", "-┴-", "-┤ ",
		" ├-", "-┬-", "-┬-", "-┬-", "-┬-", "-┬-", "-┬-", "-┬-", "-┤ ",
		" ├-", "-┼-", "-┼-", "-┼-", "-┼-", "-┼-", "-┼-", "-┼-", "-┤ ",
		" ├-", "-┼-", "-┼-", "-┼-", "-┼-", "-┼-", "-┼-", "-┼-", "-┤ ",
		" ├-", "-┼-", "-┼-", "-┼-", "-※-", "-┼-", "-┼-", "-┼-", "-┤ ",
		" └-", "-┴-", "-┴-", "-┴-", "-┴-", "-┴-", "-┴-", "-┴-", "-┘ "
	];

	var insertLine = ["",
		"\n │  │  │  │＼│／│  │  │  │ \n",
		"\n │  │  │  │／│＼│  │  │  │ \n",
		"\n │  │  │  │  │  │  │  │  │ \n",
		"\n │  │  │  │  │  │  │  │  │ \n",
		"\n │    楚  河          汉  界    │ \n",
		"\n │  │  │  │  │  │  │  │  │ \n",
		"\n │  │  │  │  │  │  │  │  │ \n",
		"\n │  │  │  │＼│／│  │  │  │ \n",
		"\n │  │  │  │／│＼│  │  │  │ \n"
	];

	for (var i = 0; i < 90; ++i) {
		i % 9 === 0 && text.push(insertLine[i / 9]);
		text.push(board[i] === "*" ? boardText[i] : piece(board[i]));
	}

	text.push(isB ? "\n\n红方" : "\n\n红方 走棋方");
	return text.join("").replace(/--/g, "─");
};

// 字符串清除标签
vschess.stripTags = function(str){
	return $('<div>' + str + '</div>').text();
};

// 时间格式统一
vschess.dateFormat = function(date){
	if (/^([0-9]{8})$/.test(date)) {
		return date.substring(0, 4) + "-" + date.substring(4, 6) + "-" + date.substring(6, 8);
	}

	return date;
};

// 替换不间断空格
vschess.replaceNbsp = function(str){
	return str.replace(new RegExp(vschess.fcc(160), "g"), " ");
};

// 长 Fen 串变短 Fen 串
vschess.shortFen = function(fen){
	return fen.split(' ')[0] + ' ' + fen.split(' ')[1];
};

// ArrayBuffer 转换为 UTF-8 字符串
vschess.UTF8 = function(array){
	var result = [];

	for (var i = 0; i < array.length; ++i) {
		if (array[i] < 16) {
			result.push("%0", array[i].toString(16));
		}
		else {
			result.push("%" , array[i].toString(16));
		}
	}

	try {
		return decodeURIComponent(result.join(""));
	}
	catch (e) {
		return ""; 
	}
};

// 将 ArrayBuffer 转换为 UTF-8 字符串
vschess.iconv2UTF8 = function(array){
	return vschess.UTF8(array);
};

// 简单合并，不做处理
vschess.join = function (array) {
  var result = [];

  for (var i = 0; i < array.length; ++i) {
    result.push(vschess.fcc(array[i]));
  }

  return result
    .join("")
    .replace("\r\n", "\n")
    .split("\n")
    .filter((line) => line.startsWith("["))
    .join("\n");
};

// 动态加载 CSS，用 Zepto 或 jQuery 方式加载的外部 CSS 在低版本 IE 下不生效，所以使用原生方法
vschess.addCSS = function(options, type, href){
	var link = document.createElement("link");
	var head = document.getElementsByTagName("head");
	typeof vschess. styleLoadedCallback[options.style ] === "undefined" && (vschess. styleLoadedCallback[options.style ] = []);
	typeof vschess.layoutLoadedCallback[options.layout] === "undefined" && (vschess.layoutLoadedCallback[options.layout] = []);
	link.setAttribute("rel", "stylesheet");
	link.setAttribute("type", "text/css");
	link.setAttribute("href", href);

	link.onload = function(){
		if (type === "global") {
			for (var i = 0; i < vschess.globalLoadedCallback.length; ++i) {
				typeof vschess.globalLoadedCallback[i] === "function" && vschess.globalLoadedCallback[i]();
			}

			vschess.globalLoaded = true;
		}

		if (type === "style") {
			for (var i = 0; i < vschess.styleLoadedCallback[options.style].length; ++i) {
				typeof vschess.styleLoadedCallback[options.style][i] === "function" && vschess.styleLoadedCallback[options.style][i]();
			}

			vschess.styleLoaded[options.style] = true;
		}

		if (type === "layout") {
			for (var i = 0; i < vschess.layoutLoadedCallback[options.layout].length; ++i) {
				typeof vschess.layoutLoadedCallback[options.layout][i] === "function" && vschess.layoutLoadedCallback[options.layout][i]();
			}

			vschess.layoutLoaded[options.layout] = true;
		}
	};

	head.length ? head[0].appendChild(link) : document.documentElement.appendChild(link);
	return this;
};

// 初始化程序，加载样式
vschess.init = function(options){
	// 全局样式，统一 Web Audio API
	if (!vschess.inited) {
		vschess.AudioContext = false;
		vschess.AudioContext = vschess.AudioContext ? new vschess.AudioContext() : false;
		vschess.addCSS(options, 'global', options.globalCSS);
		vschess.inited = true;
	}

	// 风格样式
	if (!vschess.styleInit[options.style]) {
		vschess.addCSS(options, 'style', vschess.defaultPath + 'style/' + options.style + "/style.css");
		vschess.IE6Compatible_setPieceTransparent(options);
		vschess.styleInit[options.style] = true;
	}

	// 布局样式
	if (!vschess.layoutInit[options.layout]) {
		vschess.addCSS(options, 'layout', vschess.defaultPath + 'layout/' + options.layout + "/layout.css");
		vschess.layoutInit[options.layout] = true;
	}

	// 音效组件
	if (!vschess.soundInit[options.soundStyle]) {
		$.each(vschess.soundList, function(index, name){
			var soundName = options.soundStyle + "-" + name;
			var soundId   = "vschess-sound-" + soundName;
			var soundSrc  = options.soundPath ? options.soundPath + name + ".mp3" : vschess.defaultPath + 'sound/' + options.soundStyle + '/' + name + ".mp3";
			vschess.soundObject[soundName] = function(){};

			// 支持 Web Audio 的浏览器使用 Web Audio API
			if (vschess.AudioContext) {
				var xhr = new XMLHttpRequest();
				xhr.open("GET", soundSrc, true);
				xhr.responseType = "arraybuffer";

				xhr.onload = function(){
					vschess.AudioContext.decodeAudioData(this.response, function(buffer){
						vschess.soundObject[soundName] = function(volume){
							var source   = vschess.AudioContext.createBufferSource();
							var gainNode = vschess.AudioContext.createGain();
							source.buffer = buffer;
							source.connect(vschess.AudioContext.destination);
							source.connect(gainNode);
							gainNode.connect(vschess.AudioContext.destination);
							gainNode.gain.value = volume / 50 - 1;
							source.start(0);
						};
					});
				};

				xhr.send();
			}

			// 低版本 IE 下利用 Windows Media Player 来实现走子音效
			else if (window.ActiveXObject) {
				var soundHTML = '<object id="' + soundId + '" classid="clsid:6BF52A52-394A-11d3-B153-00C04F79FAA6" style="display:none;">';
				$("body").append(soundHTML + '<param name="url" value="' + soundSrc + '" /><param name="autostart" value="false" /></object>');
				var soundObject = document.getElementById(soundId);

				vschess.soundObject[soundName] = function(volume){
					soundObject.settings.volume = volume;
					soundObject.controls.stop();
					soundObject.controls.play();
				};
			}

			// 其他浏览器通过 HTML5 中的 audio 标签来实现走子音效
			else {
				$("body").append('<audio id="' + soundId + '" src="' + soundSrc + '" preload="auto"></audio>');
				var soundObject = document.getElementById(soundId);

				vschess.soundObject[soundName] = function(volume){
					soundObject.volume = volume / 100;
					soundObject.pause();
					soundObject.currentTime = 0;
					soundObject.play();
				}
			}
		});

		vschess.soundInit[options.soundStyle] = true;
	}

	return this;
};

// 将军检查器
vschess.checkThreat = function(situation){
    if (typeof situation === "string") {
		var RegExp = vschess.RegExp();
		RegExp.FenShort.test(situation) && (situation = vschess.fenToSituation(situation));
	}

    situation = situation.slice(0);
	var kingIndex = 0;
	var player = situation[0];
	var enermy = 3 - player;

	// 寻找帅、将
	if (player === 1) {
		for (var i = 0; !kingIndex && i < 9; ++i) {
			situation[vschess.castleR[i]] === 21 && (kingIndex = vschess.castleR[i]);
		}
	}
	else {
		for (var i = 0; !kingIndex && i < 9; ++i) {
			situation[vschess.castleB[i]] === 37 && (kingIndex = vschess.castleB[i]);
		}
	}

	// 车、将、帅
	for (var k = 0; k < 4; ++k) {
		for (var i = kingIndex + vschess.kingDelta[k]; situation[i]; i += vschess.kingDelta[k]) {
			if (situation[i] > 1) {
				if (((situation[i] & 15) === 1 || (situation[i] & 15) === 5) && situation[i] >> 4 === enermy) {
					return true;
				}

				break;
			}
		}
	}

	// 马
	for (var i = 0; i < 4; ++i) {
		if (situation[kingIndex + vschess.advisorDelta[i]] === 1) {
			var piece = situation[kingIndex + vschess.knightCheckDelta[i][0]];

			if ((piece & 15) === 2 && piece >> 4 === enermy) {
				return true;
			}

			var piece = situation[kingIndex + vschess.knightCheckDelta[i][1]];

			if ((piece & 15) === 2 && piece >> 4 === enermy) {
				return true;
			}
		}
	}

	// 炮
	for (var k = 0; k < 4; ++k) {
		var barbette = false;

		for (var i = kingIndex + vschess.kingDelta[k]; situation[i]; i += vschess.kingDelta[k]) {
			if (barbette) {
				if (situation[i] > 1) {
					if ((situation[i] & 15) === 6 && situation[i] >> 4 === enermy) {
						return true;
					}

					break;
				}
			}
			else {
				situation[i] > 1 && (barbette = true);
			}
		}
	}

	// 兵、卒
	if ((situation[kingIndex + 1] & 15) === 7 && situation[kingIndex + 1] >> 4 === enermy) {
		return true;
	}

	if ((situation[kingIndex - 1] & 15) === 7 && situation[kingIndex - 1] >> 4 === enermy) {
		return true;
	}

	if (player === 1) {
		if ((situation[kingIndex - 16] & 15) === 7 && situation[kingIndex - 16] >> 4 === 2) {
			return true;
		}
	}
	else {
		if ((situation[kingIndex + 16] & 15) === 7 && situation[kingIndex + 16] >> 4 === 1) {
			return true;
		}
	}

	return false;
};

// 检查局面是否有合法着法（未被将杀或困毙）
vschess.hasLegalMove = function(situation){
	if (typeof situation === "string") {
		var RegExp = vschess.RegExp();
		RegExp.FenShort.test(situation) && (situation = vschess.fenToSituation(situation));
	}

	var player = situation[0];
	var enermy = 3 - player;

	function checkMove(src, dst) {
		var s  = situation.slice(0);
		s[dst] = s[src];
		s[src] = 1;
		return !vschess.checkThreat(s);
	}

	// 棋盘搜索边界
	for (var i = 51; i < 204; ++i) {
		if (situation[i] >> 4 !== player) {
			continue;
		}

		var piece = situation[i] & 15;

		// 车
		if (piece === 1) {
			for (var k = 0; k < 4; ++k) {
				for (var j = i + vschess.kingDelta[k]; situation[j]; j += vschess.kingDelta[k]) {
					if (situation[j] === 1) {
						if (checkMove(i, j)) return true;
						continue;
					}

					if (situation[j] >> 4 === enermy && checkMove(i, j)) return true;
					break;
				}
			}
		}

		// 马
		else if (piece === 2) {
			for (var j = 0; j < 4; ++j) {
				if (situation[i + vschess.kingDelta[j]] === 1) {
					var targetIndex0 = i + vschess.knightDelta[j][0];
					var targetIndex1 = i + vschess.knightDelta[j][1];
					if (situation[targetIndex0] && situation[targetIndex0] >> 4 !== player && checkMove(i, targetIndex0)) return true;
					if (situation[targetIndex1] && situation[targetIndex1] >> 4 !== player && checkMove(i, targetIndex1)) return true;
				}
			}
		}

		// 相、象
		else if (piece === 3) {
			// 红方相
			if (player === 1) {
				for (var j = 0; j < 4; ++j) {
					if (situation[i + vschess.advisorDelta[j]] === 1) {
						var targetIndex = i + (vschess.advisorDelta[j] << 1);
						if (situation[targetIndex] >> 4 !== player && targetIndex > 127 && checkMove(i, targetIndex)) return true;
					}
				}
			}

			// 黑方象
			else {
				for (var j = 0; j < 4; ++j) {
					if (situation[i + vschess.advisorDelta[j]] === 1) {
						var targetIndex = i + (vschess.advisorDelta[j] << 1);
						if (situation[targetIndex] >> 4 !== player && targetIndex < 127 && checkMove(i, targetIndex)) return true;
					}
				}
			}
		}

		// 仕、士
		else if (piece === 4) {
			for (var j = 0; j < 4; ++j) {
				var targetIndex = i + vschess.advisorDelta[j];
				if (vschess.castle[targetIndex] && situation[targetIndex] >> 4 !== player && checkMove(i, targetIndex)) return true;
			}
		}

		// 帅、将
		else if (piece === 5) {
			for (var k = 0; k < 4; ++k) {
				var targetIndex = i + vschess.kingDelta[k];
				if (vschess.castle[targetIndex] && situation[targetIndex] >> 4 !== player && checkMove(i, targetIndex)) return true;
			}
		}

		// 炮
		else if (piece === 6) {
			for (var k = 0; k < 4; ++k) {
				var barbette = false;

				for (var j = i + vschess.kingDelta[k]; situation[j]; j += vschess.kingDelta[k]) {
					if (barbette) {
						if (situation[j] === 1) {
							continue;
						}

						if (situation[j] >> 4 === enermy && checkMove(i, j)) return true;
						break;
					}
					else {
						if (situation[j] === 1) {
							if (checkMove(i, j)) return true;
						}
						else {
							barbette = true;
						}
					}
				}
			}
		}

		// 兵、卒
		else  {
			// 红方兵
			if (player === 1) {
				if (situation[i - 16] && situation[i - 16] >> 4 !== 1 &&			checkMove(i, i - 16)) return true;
				if (situation[i +  1] && situation[i +  1] >> 4 !== 1 && i < 128 &&	checkMove(i, i +  1)) return true;
				if (situation[i -  1] && situation[i -  1] >> 4 !== 1 && i < 128 &&	checkMove(i, i -  1)) return true;
			}

			// 黑方卒
			else {
				if (situation[i + 16] && situation[i + 16] >> 4 !== 2 &&			checkMove(i, i + 16)) return true;
				if (situation[i -  1] && situation[i -  1] >> 4 !== 2 && i > 127 &&	checkMove(i, i -  1)) return true;
				if (situation[i +  1] && situation[i +  1] >> 4 !== 2 && i > 127 &&	checkMove(i, i +  1)) return true;
			}
		}
	}

	return false;
};

// 着法生成器（索引模式）
vschess.legalList = function(situation){
	if (typeof situation === "string") {
		var RegExp = vschess.RegExp();
		RegExp.FenShort.test(situation) && (situation = vschess.fenToSituation(situation));
	}

	var legalList = [];
	var player = situation[0];
	var enermy = 3 - player;

	function checkPush(step) {
		var s = situation.slice(0);
		s[step[1]] = s[step[0]];
		s[step[0]] = 1;
		vschess.checkThreat(s) || legalList.push(step);
	}

	// 棋盘搜索边界
	for (var i = 51; i < 204; ++i) {
		if (situation[i] >> 4 !== player) {
			continue;
		}

		var piece = situation[i] & 15;

		// 车
		if (piece === 1) {
			for (var k = 0; k < 4; ++k) {
				for (var j = i + vschess.kingDelta[k]; situation[j]; j += vschess.kingDelta[k]) {
					if (situation[j] === 1) {
						checkPush([i, j]);
						continue;
					}

					situation[j] >> 4 === enermy && checkPush([i, j]);
					break;
				}
			}
		}

		// 马
		else if (piece === 2) {
			for (var j = 0; j < 4; ++j) {
				if (situation[i + vschess.kingDelta[j]] === 1) {
					var targetIndex0 = i + vschess.knightDelta[j][0];
					var targetIndex1 = i + vschess.knightDelta[j][1];
					situation[targetIndex0] && situation[targetIndex0] >> 4 !== player && checkPush([i, targetIndex0]);
					situation[targetIndex1] && situation[targetIndex1] >> 4 !== player && checkPush([i, targetIndex1]);
				}
			}
		}

		// 相、象
		else if (piece === 3) {
			// 红方相
			if (player === 1) {
				for (var j = 0; j < 4; ++j) {
					if (situation[i + vschess.advisorDelta[j]] === 1) {
						var targetIndex = i + (vschess.advisorDelta[j] << 1);
						situation[targetIndex] >> 4 !== player && targetIndex > 127 && checkPush([i, targetIndex]);
					}
				}
			}

			// 黑方象
			else {
				for (var j = 0; j < 4; ++j) {
					if (situation[i + vschess.advisorDelta[j]] === 1) {
						var targetIndex = i + (vschess.advisorDelta[j] << 1);
						situation[targetIndex] >> 4 !== player && targetIndex < 127 && checkPush([i, targetIndex]);
					}
				}
			}
		}

		// 仕、士
		else if (piece === 4) {
			for (var j = 0; j < 4; ++j) {
				var targetIndex = i + vschess.advisorDelta[j];
				vschess.castle[targetIndex] && situation[targetIndex] >> 4 !== player && checkPush([i, targetIndex]);
			}
		}

		// 帅、将
		else if (piece === 5) {
			for (var k = 0; k < 4; ++k) {
				var targetIndex = i + vschess.kingDelta[k];
				vschess.castle[targetIndex] && situation[targetIndex] >> 4 !== player && checkPush([i, targetIndex]);
			}
		}

		// 炮
		else if (piece === 6) {
			for (var k = 0; k < 4; ++k) {
				var barbette = false;

				for (var j = i + vschess.kingDelta[k]; situation[j]; j += vschess.kingDelta[k]) {
					if (barbette) {
						if (situation[j] === 1) {
							continue;
						}

						situation[j] >> 4 === enermy && checkPush([i, j]);
						break;
					}
					else {
						situation[j] === 1 ? checkPush([i, j]) : barbette = true;
					}
				}
			}
		}

		// 兵、卒
		else  {
			// 红方兵
			if (player === 1) {
				situation[i - 16] && situation[i - 16] >> 4 !== 1 &&			checkPush([i, i - 16]);
				situation[i +  1] && situation[i +  1] >> 4 !== 1 && i < 128 &&	checkPush([i, i +  1]);
				situation[i -  1] && situation[i -  1] >> 4 !== 1 && i < 128 &&	checkPush([i, i -  1]);
			}

			// 黑方卒
			else {
				situation[i + 16] && situation[i + 16] >> 4 !== 2 &&			checkPush([i, i + 16]);
				situation[i -  1] && situation[i -  1] >> 4 !== 2 && i > 127 &&	checkPush([i, i -  1]);
				situation[i +  1] && situation[i +  1] >> 4 !== 2 && i > 127 &&	checkPush([i, i +  1]);
			}
		}
	}

	return legalList;
};

// 着法生成器（坐标模式）
vschess.legalMoveList = function(situation){
	if (typeof situation === "string") {
		var RegExp = vschess.RegExp();
		RegExp.FenShort.test(situation) && (situation = vschess.fenToSituation(situation));
	}

	var legalList = vschess.legalList(situation), result = [];

	for (var i = 0; i < legalList.length; ++i) {
		result.push(vschess.s2i[legalList[i][0]] + vschess.s2i[legalList[i][1]]);
	}

	return result;
};

// Fen 串合法性检查，返回错误列表，列表长度为 0 表示没有错误
vschess.checkFen = function(fen){
	var RegExp = vschess.RegExp();

	if (!RegExp.FenShort.test(fen)) {
		return ["Fen 串不合法"];
	}

	var errorList = [], board = vschess.fenToArray(fen), Kk = false;
	var total = { R: 0, N: 0, B: 0, A: 0, K: 0, C: 0, P: 0, r: 0, n: 0, b: 0, a: 0, k: 0, c: 0, p: 0, "*": 0 };

	function push(error){
		~errorList.indexOf(error) || errorList.push(error);
	}

	for (var i = 0; i < 90; ++i) {
		board[i] === "K" && !~[ 66, 67, 68, 75, 76, 77, 84, 85, 86 ].indexOf(i    )  && push("红方帅的位置不符合规则");
		board[i] === "k" && !~[  3,  4,  5, 12, 13, 14, 21, 22, 23 ].indexOf(i    )  && push("黑方将的位置不符合规则");
		board[i] === "B" && !~[     47, 51, 63, 67, 71, 83, 87     ].indexOf(i    )  && push("红方相的位置不符合规则");
		board[i] === "b" && !~[      2,  6, 18, 22, 26, 38, 42     ].indexOf(i    )  && push("黑方象的位置不符合规则");
		board[i] === "A" && !~[         66, 68, 76, 84, 86         ].indexOf(i    )  && push("红方仕的位置不符合规则");
		board[i] === "a" && !~[          3,  5, 13, 21, 23         ].indexOf(i    )  && push("黑方士的位置不符合规则");
		board[i] === "P" && (i >= 63 || i >= 45 && !~[0, 2, 4, 6, 8].indexOf(i % 9)) && push("红方兵的位置不符合规则");
		board[i] === "p" && (i <  27 || i <  45 && !~[0, 2, 4, 6, 8].indexOf(i % 9)) && push("黑方卒的位置不符合规则");

		++total[board[i]];

		if (board[i] === "K") {
			for (var j = i - 9; j > 0; j -= 9) {
				if (board[j] !== "*") {
					board[j] === "k" && (Kk = true) && push("帅将面对面了");
					break;
				}
			}
		}
	}

	board[45] === "P" && board[54] === "P" && push("红方九路出现未过河的重叠兵");
	board[47] === "P" && board[56] === "P" && push("红方七路出现未过河的重叠兵");
	board[49] === "P" && board[58] === "P" && push("红方五路出现未过河的重叠兵");
	board[51] === "P" && board[60] === "P" && push("红方三路出现未过河的重叠兵");
	board[53] === "P" && board[62] === "P" && push("红方一路出现未过河的重叠兵");
	board[27] === "p" && board[36] === "p" && push("黑方１路出现未过河的重叠卒");
	board[29] === "p" && board[38] === "p" && push("黑方３路出现未过河的重叠卒");
	board[31] === "p" && board[40] === "p" && push("黑方５路出现未过河的重叠卒");
	board[33] === "p" && board[42] === "p" && push("黑方７路出现未过河的重叠卒");
	board[35] === "p" && board[44] === "p" && push("黑方９路出现未过河的重叠卒");

	total.R > 2 && push("红方出现了" + total.R + "个车，多了" + (total.R - 2) + "个");
	total.r > 2 && push("黑方出现了" + total.r + "个车，多了" + (total.r - 2) + "个");
	total.N > 2 && push("红方出现了" + total.N + "个马，多了" + (total.N - 2) + "个");
	total.n > 2 && push("黑方出现了" + total.n + "个马，多了" + (total.n - 2) + "个");
	total.B > 2 && push("红方出现了" + total.B + "个相，多了" + (total.B - 2) + "个");
	total.b > 2 && push("黑方出现了" + total.b + "个象，多了" + (total.b - 2) + "个");
	total.A > 2 && push("红方出现了" + total.A + "个仕，多了" + (total.A - 2) + "个");
	total.a > 2 && push("黑方出现了" + total.a + "个士，多了" + (total.a - 2) + "个");
	total.C > 2 && push("红方出现了" + total.C + "个炮，多了" + (total.C - 2) + "个");
	total.c > 2 && push("黑方出现了" + total.c + "个炮，多了" + (total.c - 2) + "个");
	total.P > 5 && push("红方出现了" + total.P + "个兵，多了" + (total.P - 5) + "个");
	total.p > 5 && push("黑方出现了" + total.p + "个卒，多了" + (total.p - 5) + "个");
	total.K > 1 && push("红方出现了" + total.K + "个帅，多了" + (total.K - 1) + "个");
	total.k > 1 && push("黑方出现了" + total.k + "个将，多了" + (total.k - 1) + "个");
	total.K < 1 && push("红方必须有一个帅");
	total.k < 1 && push("黑方必须有一个将");

	if (!Kk) {
		if (vschess.checkThreat(fen) && vschess.checkThreat(vschess.fenChangePlayer(fen))) {
			push("红黑双方同时被将军");
		}
		else if (vschess.checkThreat(vschess.fenChangePlayer(fen))) {
			fen.split(" ")[1] === "b" ? push("轮到黑方走棋，但此时红方正在被将军") : push("轮到红方走棋，但此时黑方正在被将军");
		}
	}

	return errorList;
};

// 是否有杀棋着法
vschess.hasKillMove = function(situation){
	if (typeof situation === "string") {
		var RegExp = vschess.RegExp();
		RegExp.FenShort.test(situation) && (situation = vschess.fenToSituation(situation));
	}

	var legalList = vschess.legalList(situation);

	for (var i = 0; i < legalList.length; ++i) {
		var movedSituation = situation.slice(0);
		movedSituation[legalList[i][1]] = movedSituation[legalList[i][0]];
		movedSituation[legalList[i][0]] = 1;
		movedSituation[0] = 3 - movedSituation[0];

		if (vschess.checkThreat(movedSituation) && !vschess.hasLegalMove(movedSituation)) {
			return true;
		}
	}

	return false;
};

// 叫杀检查器
vschess.checkKill = function(fen){
	var RegExp = vschess.RegExp();
	RegExp.FenShort.test(fen) || (fen = vschess.defaultFen);
	return vschess.checkThreat(fen) ? false : vschess.hasKillMove(vschess.fenChangePlayer(fen));
};

// 计算长打着法
vschess.repeatLongThreatMove = function(moveList){
	if (moveList.length < 13) {
		return [];
	}

	var fenList = [moveList[0]];

	for (var i = 1; i < moveList.length; ++i) {
		fenList.push(vschess.fenMovePiece(fenList[i - 1], moveList[i]))
	}

	var threatFenList = {};

	for (var i = fenList.length - 2; i >= 0; i -= 2) {
		if (vschess.checkThreat(fenList[i])) {
			if (vschess.checkThreat(fenList[i + 1])) {
				break;
			}

			var shortFen = fenList[i].split(" ", 2).join(" ");
			shortFen in threatFenList ? ++threatFenList[shortFen] : (threatFenList[shortFen] = 1);
		}
		else {
			break;
		}
	}

	if (fenList.length - i < 14) {
		return [];
	}

	var lastFen		= fenList[fenList.length - 1];
	var legalList	= vschess.legalMoveList(lastFen);
	var banMoveList	= [];
	var canMoveList	= [];

	for (var i = 0; i < legalList.length; ++i) {
		var move     = legalList[i];
		var movedFen = vschess.fenMovePiece(lastFen, move).split(" ", 2).join(" ");
		threatFenList[movedFen] >= 3 ? banMoveList.push(move) : canMoveList.push(move);
	}

	return banMoveList;
};

// 计算一将一杀着法
vschess.repeatLongKillMove = function(moveList){
	if (moveList.length < 13 || vschess.repeatLongThreatMove(moveList)) {
		return [];
	}

	var fenList = [moveList[0]];

	for (var i = 1; i < moveList.length; ++i) {
		fenList.push(vschess.fenMovePiece(fenList[i - 1], moveList[i]))
	}

	var killFenList = {};

	for (var i = fenList.length - 2; i >= 0; i -= 2) {
		if (vschess.checkThreat(fenList[i])) {
			var shortFen = fenList[i].split(" ", 2).join(" ");
			shortFen in killFenList ? ++killFenList[shortFen] : (killFenList[shortFen] = 1);
		}
		else if (vschess.checkKill(fenList[i])) {
			"kill" in killFenList ? ++killFenList["kill"] : (killFenList["kill"] = 1);
		}
		else {
			break;
		}
	}

	var lastFen		= fenList[fenList.length - 1];
	var legalList	= vschess.legalMoveList(lastFen);
	var banMoveList	= [];
	var canMoveList	= [];

	if (fenList.length - i < 14) {
		return [];
	}

	for (var i = 0; i < legalList.length; ++i) {
		var move     = legalList[i];
		var movedFen = vschess.fenMovePiece(lastFen, move).split(" ", 2).join(" ");

		if (vschess.checkKill(movedFen)) {
			killFenList["kill"] >= 3 ? banMoveList.push(move) : canMoveList.push(move);
		}
		else {
			killFenList[movedFen] >= 3 ? banMoveList.push(move) : canMoveList.push(move);
		}
	}

	return canMoveList.length ? banMoveList : [];
};

// 创建象棋组件，兼容两种创建模式：实例模式和方法模式
vschess.load = function(selector, options){
	// 实例模式下，每次运行时都只会为指定选择器中第一个未创建棋盘的 DOM 元素创建棋盘，若该选择器下有多个 DOM 元素，则需要多次运行
	// 实例模式使用举例：var chess = new vschess.load(".vschess");，返回一个棋盘对象
	if (this instanceof vschess.load) {
		var _this = this;
		this.options = $.extend(true, {}, vschess.defaultOptions, options);
		this._ = { nodeLength: 0 };
		vschess.init(this.options);
		this.originalDOM = $(selector).not(".vschess-loaded, .vschess-original-dom").first();
		this.DOM = this.originalDOM.clone();
		this.originalDOM.after(this.DOM).addClass("vschess-original-dom");
		this.createLoading(selector);

		var waitCSS = setInterval(function(){
			if (vschess.globalLoaded && vschess.layoutLoaded[_this.options.layout] && vschess.styleLoaded[_this.options.style]) {
				clearInterval(waitCSS);
				_this.createBoard();
				_this.initData();
				typeof _this["callback_loadFinish"] === "function" && _this["callback_loadFinish"]();
			}
		}, vschess.threadTimeout);

		return this;
	}

	// 方法模式下，只需运行一次，便可为该选择器下所有元素创建棋盘
	// 方法模式使用举例：var chess = vschess.load(".vschess");，返回一个包含所有棋盘对象的数组
	// 该数组可以直接调用属于每个棋盘的方法，程序将自动为所有棋盘应用此方法
	// 例如：chess.setBoardByStep(3);，将所有棋盘设置为第四个局面（越界自动修正），返回包含所有棋盘的数组，即数组本身
	// 再如：chess.isR(5);，检查所有棋盘的 index 为 5 的棋子是否为红方棋子，返回 [true, false, ......]，返回的数组长度即为棋盘数量
	else {
		var chessList = [];

		$(selector).not(".vschess-loaded, .vschess-original-dom").each(function(){
			chessList.push(new vschess.load(this, options));
		});

		$.each(vschess.load.prototype, function(name){
			chessList[name] = function(){
				var result = [];

				for (var i = 0; i < this.length; ++i) {
					result.push(vschess.load.prototype[name].apply(this[i], arguments));
				}

				name === "toString" && (result = result.toString());
				return result;
			};
		});

		return chessList;
	}
};

// 创建棋盘界面
vschess.load.prototype.createBoard = function(){
	var _this = this;
	this.DOM.children(".vschess-loading").remove();
	this.bindDrag();

	// 标题
	this.title = $('<div class="vschess-title"></div>');
	this.DOM.append(this.title);

	// 棋盘
	this.board = $('<div class="vschess-board"></div>');
	this.DOM.append(this.board);
	this.board.append(new Array(91).join('<div class="vschess-piece"><span></span></div>'));
	this.piece = this.board.children(".vschess-piece");
	this.board.append('<div class="vschess-piece-animate"><span></span></div>');
	this.animatePiece = this.board.children(".vschess-piece-animate");
	this.pieceClick();
	this.initPieceRotateDeg();

	// 其他组件
    this.createLocalDownloadLink();
    this.createChangeSelectList();
    this.createMoveSelectList();
    this.createCopyTextarea();
    this.createColumnIndex();
    this.createControlBar();
    this.createMessageBox();
    this.createFormatBar();
    this.createMobileTag();
    this.createTab();
    this.interval = { time: 0, tag: 0, run: setInterval(function(){ _this.intervalCallback(); }, 100) };
    this.chessId  = vschess.chessList.length;

	window.addEventListener("resize", function(){ _this.resetDPR(); }, false);
	vschess.chessList.push(this);
	return this;
};

// 填充初始数据
vschess.load.prototype.initData = function(){
	this.refreshColumnIndex();
	this.setSaved(true);
    this.showTab(this.options.defaultTab);
	this.initCallback();
	this.initArguments();
	this.initStart();
	return this;
};

// 初始化参数
vschess.load.prototype.initArguments = function(){
	this.setBanRepeatLongThreat	(this.options.banRepeatLongThreat	);
	this.setBanRepeatLongKill	(this.options.banRepeatLongKill		);
	this.setQuickStepOffset		(this.options.quickStepOffset		);
	this.setClickResponse		(this.options.clickResponse			);
	this.setAnimationTime		(this.options.animationTime			);
	this.setPieceRotate			(this.options.pieceRotate			);
	this.setIllegalTips			(this.options.illegalTips			);
	this.setMoveFormat			(this.options.moveFormat			);
	this.setSpeakMove			(this.options.speakMove				);
	this.setMoveTips			(this.options.moveTips				);
	this.setSaveTips			(this.options.saveTips				);
	this.setPlayGap				(this.options.playGap				);
	this.setVolume				(this.options.volume				);
	this.setSound				(this.options.sound					);
	return this;
};

// 创建加载界面
vschess.load.prototype.createLoading = function(selector){
	this.chessData = this.options.chessData === false ? this.DOM.html() : this.options.chessData;
	this.DOM.html('<div class="vschess-loading">棋盘加载中，请稍候。</div>');
	this.DOM.addClass("vschess-loaded vschess-style-" + this.options.style + " vschess-layout-" + this.options.layout);
	this.DOM.attr("data-vschess-dpr", vschess.dpr);
	return this;
};

// 初始化起始局面
vschess.load.prototype.initStart = function(){
	this.setNode(vschess.dataToNode(this.chessData, this.options.parseType));
	this.rebuildSituation();
	this.setTurn		 (this.options.turn);
	this.setBoardByStep	 (this.options.currentStep);
	this.setExportFormat ("PGN_Chinese");
	return this;
};

// 初始化回调列表
vschess.load.prototype.initCallback = function(){
	for (var i = 0; i < vschess.callbackList.length; ++i) {
		this["callback_" + vschess.callbackList[i]] = this.options[vschess.callbackList[i]] || function(){};
	}

	return this;
};

// 自动播放组件
vschess.load.prototype.intervalCallback = function(){
	if (!this.interval.time || ++this.interval.tag % this.interval.time) {
		return false;
	}

	var _this = this;
	this.animateToNext(this.getAnimationTime(), function(){ _this.getCurrentStep() >= _this.lastSituationIndex() && _this.pause(); });
	this.interval.tag = 0;
	return this;
};

// 卸载棋盘，即将对应的 DOM 恢复原状
vschess.load.prototype.unload = function(){
	this.DOM.remove();
	this.originalDOM.removeClass("vschess-original-dom");
	window.removeEventListener("resize", this.resetDPR, false);
	return this;
};

// 创建列号
vschess.load.prototype.createColumnIndex = function(){
	var columnText = this.options.ChineseChar.Number.split("");
	this.columnIndexR = $('<div class="vschess-column-index"></div>');
	this.columnIndexB = $('<div class="vschess-column-index"></div>');
	this.DOM.append(this.columnIndexR);
	this.DOM.append(this.columnIndexB);

	for (var i = 0; i < 9; ++i) {
		this.columnIndexR.append('<div class="vschess-column-index-item">' + columnText[i    ] + '</div>');
		this.columnIndexB.append('<div class="vschess-column-index-item">' + columnText[i + 9] + '</div>');
	}

	return this;
};

// 重置 DPR
vschess.load.prototype.resetDPR = function(){
	vschess.dpr = window.devicePixelRatio || 1;
	$(this.DOM).attr("data-vschess-dpr", vschess.dpr);
	return this;
};

// 将着法列表转换为文本 TXT 格式
vschess.moveListToText = function(moveList, startFen, commentList, infoList, result){
	var RegExp = vschess.RegExp();

	if (RegExp.FenShort.test(moveList[0])) {
		moveList = moveList.slice(0);
		startFen = moveList.shift();
	}
	else {
		RegExp.FenShort.test(startFen) || (startFen = vschess.defaultFen);
	}

	var startFenSplit =  startFen.split(" ");
	var startRound    = +startFenSplit[5] || 1;
	var text = ["中国象棋对局记录\n"];

	for (var i in infoList) {
		text.push(vschess.info.name[i], "：", vschess.showText(infoList[i], i), "\n");
	}

	startFen === vschess.defaultFen || text.push("开局 Fen 串：", startFen, "\n");
	text.push(commentList[0] ? "（" + commentList[0] + "）\n" : "");

	if (startFenSplit[1] === "b") {
		for (var i = 0; i < moveList.length; ++i) {
			if (i === 0) {
				var round = startRound;
				round = vschess.strpad(round, Math.ceil((moveList.length + 1) / 2).toString().length, " ", "left");
				text.push(round, ". ………… ", moveList[i], commentList[i + 1] ? "\n（" + commentList[i + 1] + "）" : "", "\n");
			}
			else {
				var round = (i + 1) / 2 + startRound;
				round = vschess.strpad(round, Math.ceil((moveList.length + 1) / 2).toString().length, " ", "left");
				i % 2 && text.push(round, ". ");
				text.push(moveList[i], commentList[i + 1] ? "\n（" + commentList[i + 1] + "）" : "");
				commentList[i + 1] && i % 2 && i != moveList.length - 1 && text.push("\n", round, ". …………");
				text.push(i % 2 ? " " : "\n");
			}
		}
	}
	else {
		for (var i = 0; i < moveList.length; ++i) {
			var round = i / 2 + startRound;
			round = vschess.strpad(round, Math.ceil(moveList.length / 2).toString().length, " ", "left");
			i % 2 || text.push(round, ". ");
			text.push(moveList[i], commentList[i + 1] ? "\n（" + commentList[i + 1] + "）" : "");
			commentList[i + 1] && !(i % 2) && i != moveList.length - 1 && text.push("\n", round, ". …………");
			text.push(i % 2 ? "\n" : " ");
		}
	}

	text = $.trim(text.join(""));
	var resultStr = vschess.showText(result, "result");

	if (resultStr) {
		if (text.split("").pop() === "）") {
			text += "\n" + resultStr;
		}
		else {
			(startFenSplit[1] === "b") === !!(moveList.length % 2) && (text += "\n");
			text += resultStr;
		}
	}

	return text;
};

// 将棋谱节点树转换为东萍象棋 DhtmlXQ 格式
vschess.nodeToData_DhtmlXQ = function(nodeData, infoList, isMirror){
	var DhtmlXQ_binit = [99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99, 99];
	var DhtmlXQ   = ["[DhtmlXQ]"];
	var fenSplit  = nodeData.fen.split(" ");
	var pieceEach = fenSplit[0]
		.replace(/1/g,"*")
		.replace(/2/g,"**")
		.replace(/3/g,"***")
		.replace(/4/g,"****")
		.replace(/5/g,"*****")
		.replace(/6/g,"******")
		.replace(/7/g,"*******")
		.replace(/8/g,"********")
		.replace(/9/g,"*********")
		.replace(/\//g,"").split("");

	for (var i in infoList) {
		DhtmlXQ.push('[DhtmlXQ_' + (vschess.info.DhtmlXQ[i] || i) + ']' + vschess.showText(infoList[i], i) + '[/DhtmlXQ_' + (vschess.info.DhtmlXQ[i] || i) + ']');
	}

	for (var i = 0; i < 90; ++i) {
		var position = i % 9 * 10 + Math.floor(i / 9);
		position < 10 && (position = "0" + position);

		switch (pieceEach[i]) {
			case "K": DhtmlXQ_binit[ 4] = position; break;
			case "k": DhtmlXQ_binit[20] = position; break;
			case "R": DhtmlXQ_binit[ 0] === 99 ? DhtmlXQ_binit[ 0] = position : DhtmlXQ_binit[ 8] = position; break;
			case "N": DhtmlXQ_binit[ 1] === 99 ? DhtmlXQ_binit[ 1] = position : DhtmlXQ_binit[ 7] = position; break;
			case "B": DhtmlXQ_binit[ 2] === 99 ? DhtmlXQ_binit[ 2] = position : DhtmlXQ_binit[ 6] = position; break;
			case "A": DhtmlXQ_binit[ 3] === 99 ? DhtmlXQ_binit[ 3] = position : DhtmlXQ_binit[ 5] = position; break;
			case "C": DhtmlXQ_binit[ 9] === 99 ? DhtmlXQ_binit[ 9] = position : DhtmlXQ_binit[10] = position; break;
			case "r": DhtmlXQ_binit[16] === 99 ? DhtmlXQ_binit[16] = position : DhtmlXQ_binit[24] = position; break;
			case "n": DhtmlXQ_binit[17] === 99 ? DhtmlXQ_binit[17] = position : DhtmlXQ_binit[23] = position; break;
			case "b": DhtmlXQ_binit[18] === 99 ? DhtmlXQ_binit[18] = position : DhtmlXQ_binit[22] = position; break;
			case "a": DhtmlXQ_binit[19] === 99 ? DhtmlXQ_binit[19] = position : DhtmlXQ_binit[21] = position; break;
			case "c": DhtmlXQ_binit[25] === 99 ? DhtmlXQ_binit[25] = position : DhtmlXQ_binit[26] = position; break;
			case "P": {
				for (var j = 11; j < 16; ++j) {
					if (DhtmlXQ_binit[j] === 99) {
						DhtmlXQ_binit[j] = position;
						break;
					}
				}

				break;
			}
			case "p": {
				for (var j = 27; j < 32; ++j) {
					if (DhtmlXQ_binit[j] === 99) {
						DhtmlXQ_binit[j] = position;
						break;
					}
				}

				break;
			}
		}
	}

	DhtmlXQ.push("[DhtmlXQ_fen]"   + nodeData.fen           + "[/DhtmlXQ_fen]"  );
	DhtmlXQ.push("[DhtmlXQ_binit]" + DhtmlXQ_binit.join("") + "[/DhtmlXQ_binit]");
	var branchList = [], parentIndexList = [], parentStepsList = [], resultList = [], commentResult = [], branchIndex = 0;

	function makeBranch(){
		var step = 1;
		var node = branchList.pop();
		var parentIndex  = parentIndexList.pop();
		var parentSteps  = parentStepsList.pop();
		var branchResult = ["[DhtmlXQ_move_", parentIndex, "_", parentSteps, "_", branchIndex, "]"];
		var moveSplit    = node.move.split("");
		moveSplit[0] 	 = vschess.cca(moveSplit[0]) - 97;
		moveSplit[2] 	 = vschess.cca(moveSplit[2]) - 97;
		moveSplit[1] 	 = 9 - moveSplit[1];
		moveSplit[3] 	 = 9 - moveSplit[3];
		branchResult.push(moveSplit.join(""));
		node.comment && commentResult.push(["[DhtmlXQ_comment", branchIndex, "_", parentSteps, "]", node.comment.replace(/\n/g, "||"), "[/DhtmlXQ_comment", branchIndex, "_", parentSteps, "]"].join(""));

		while (node.next.length) {
			for (var i = node.next.length - 1; i >= 0; --i) {
				if (i !== node.defaultIndex) {
					branchList.push(node.next[i]);
					parentIndexList.push(branchIndex);
					parentStepsList.push(parentSteps + step);
				}
			}

			node = node.next[node.defaultIndex];
			moveSplit = node.move.split("");
			moveSplit[0] = moveSplit[0].charCodeAt(0) - 97;
			moveSplit[2] = moveSplit[2].charCodeAt(0) - 97;
			moveSplit[1] = 9 - moveSplit[1];
			moveSplit[3] = 9 - moveSplit[3];
			branchResult.push(moveSplit.join(""));
			node.comment && commentResult.push(["[DhtmlXQ_comment", branchIndex, "_", parentSteps + step, "]", node.comment.replace(/\n/g, "||"), "[/DhtmlXQ_comment", branchIndex, "_", parentSteps + step, "]"].join(""));
			++step;
		}

		branchResult.push("[/DhtmlXQ_move_", parentIndex, "_", parentSteps, "_", branchIndex, "]");
		resultList.push(branchResult.join(""));
		++branchIndex;
		branchList.length && makeBranch();
	}

	for (var i = nodeData.next.length - 1; i >= 0; --i) {
		if (i !== nodeData.defaultIndex) {
			branchList.push(nodeData.next[i]);
			parentIndexList.push(0);
			parentStepsList.push(1);
		}
	}

	nodeData.next.length && branchList.push(nodeData.next[nodeData.defaultIndex]);
	parentIndexList.push(0);
	parentStepsList.push(1);
	nodeData.comment && commentResult.push(["[DhtmlXQ_comment0]", nodeData.comment.replace(/\n/g, "||"), "[/DhtmlXQ_comment0]"].join(""));
	branchList.length && makeBranch();
	resultList.length && DhtmlXQ.push(resultList.join("\n").replace("[DhtmlXQ_move_0_1_0]", "[DhtmlXQ_movelist]").replace("[/DhtmlXQ_move_0_1_0]", "[/DhtmlXQ_movelist]"));
	commentResult.length && DhtmlXQ.push(commentResult.join("\n").replace(/DhtmlXQ_comment0_/g, "DhtmlXQ_comment"));
	DhtmlXQ.push("[/DhtmlXQ]");
	return isMirror ? vschess.turn_DhtmlXQ(DhtmlXQ.join("\n")) : DhtmlXQ.join("\n");
};

// 翻转东萍象棋 DhtmlXQ 格式
vschess.turn_DhtmlXQ = function(chessData){
	var DhtmlXQ_EachLine = chessData.split("\n");

	for (var i = 0; i < DhtmlXQ_EachLine.length; ++i) {
		var l = DhtmlXQ_EachLine[i];

		if (~l.indexOf("[DhtmlXQ_binit")) {
			var startSplit = l.substring(l.indexOf("[DhtmlXQ_binit") + 15, l.indexOf("[/DhtmlXQ_")).split("");

			for (var j = 0; j < startSplit.length; j += 2) {
				startSplit[j] < 9 && (startSplit[j] = 8 - startSplit[j]);
			}

			DhtmlXQ_EachLine[i] = "[DhtmlXQ_binit]" + startSplit.join("") + "[/DhtmlXQ_binit]";
		}
		else if (~l.indexOf("[DhtmlXQ_movelist")) {
			var moveSplit = l.substring(l.indexOf("[DhtmlXQ_movelist") + 18, l.indexOf("[/DhtmlXQ_")).split("");

			for (var j = 0; j < moveSplit.length; j += 2) {
				moveSplit[j] < 9 && (moveSplit[j] = 8 - moveSplit[j]);
			}

			DhtmlXQ_EachLine[i] = "[DhtmlXQ_movelist]" + moveSplit.join("") + "[/DhtmlXQ_movelist]";
		}
		else if (~l.indexOf("[DhtmlXQ_move_")) {
			var start		= l.indexOf("]");
			var changeId	= l.substring(14, start);
			var changeSplit = l.substring(start + 1, l.indexOf("[/DhtmlXQ_")).split("");

			for (var j = 0; j < changeSplit.length; j += 2) {
				changeSplit[j] < 9 && (changeSplit[j] = 8 - changeSplit[j]);
			}

			DhtmlXQ_EachLine[i] = "[DhtmlXQ_move_" + changeId + "]" + changeSplit.join("") + "[/DhtmlXQ_move_" + changeId + "]";
		}
	}

	return DhtmlXQ_EachLine.join("\n");
};

// 节点 ICCS 转换为中文着法（兼容 WXF 着法转换为中文着法，直接返回结果字符串）
vschess.Node2Chinese = function(move, fen, options){
	var RegExp = vschess.RegExp();
	RegExp.FenShort.test(fen) || (fen = vschess.defaultFen);
	typeof options === "undefined" && (options = vschess.defaultOptions);
	var w2i = [{ "+": 0, ".": 1, "-": 2 }, { "+": 3, "-": 4, ".": 5 }];
	var isB = fen.split(" ")[1] === "b", result = "";
	var isWXFMove = ~"+-.".indexOf(move.charAt(2));

	if (isWXFMove) {
		var wxfSplit = move.replace(/^([RNHBEAKCP])([\+\-])/g, "$2$1").replace("Pa", "1P").replace("Pb", "2P").replace("Pc", "3P").replace("Pd", "4P").replace("Pe", "5P").replace(/^P\./, ".P").split("");
	}
	else {
		var wxfData  = vschess.Node2WXF(move, fen);

		if (wxfData.move === "None") {
			return { move: "无效着法", movedFen: vschess.defaultFen };
		}
		else {
			var wxfSplit = wxfData.move.replace(/^([RNHBEAKCP])([\+\-])/g, "$2$1").replace("Pa", "1P").replace("Pb", "2P").replace("Pc", "3P").replace("Pd", "4P").replace("Pe", "5P").replace(/^P\./, ".P").split("");
		}
	}

	// 将 WXF 格式转换为中文格式，看起来眼晕@_@？（这里你用不着看懂，想看懂得可以去看官方文档，那里有这一段的最原始代码。）
	result += vschess.cca(wxfSplit[0]) > 47 ? isNaN(wxfSplit[0]) ? options.ChineseChar.Piece.charAt((vschess.f2n[wxfSplit[0]] & 15) + (isB ? 6 : -1)) : options.ChineseChar.PawnIndex.charAt(wxfSplit[0] - (isB ? -4 : 1)) : options.ChineseChar.Text.charAt(w2i[0][wxfSplit[0]]);
	result += isNaN(wxfSplit[1]) ? options.ChineseChar.Piece.charAt((vschess.f2n[wxfSplit[1]] & 15) - (isB ? -6 : 1)) : options.ChineseChar.Number.charAt(wxfSplit[1] - (isB ? -8 : 1));
	result += options.ChineseChar.Text.charAt(w2i[1][wxfSplit[2]]) + options.ChineseChar.Number.charAt(wxfSplit[3] - (isB ? -8 : 1));

	if (isWXFMove) {
		return result;
	}

	return { move: result, movedFen: wxfData.movedFen };
};

// 节点 ICCS 转换为 WXF 着法
vschess.Node2WXF = function(move, fen){
	var RegExp = vschess.RegExp();
	RegExp.FenShort.test(fen) || (fen = vschess.defaultFen);
	var isB = fen.split(" ")[1] === "b";
	move = move.toLowerCase();

	// 黑方旋转处理
	if (isB) {
		var step	  = vschess.roundMove(move);
		var situation = vschess.fenToSituation(vschess.roundFen(fen));
	}
	// 红方直接处理
	else {
		var step	  = move;
		var situation = vschess.fenToSituation(fen);
	}

	var from	= vschess.i2s[step.substring(0, 2)];
	var to		= vschess.i2s[step.substring(2, 4)];

	if (situation[from] < 16) {
		return { move: "None", movedFen: vschess.defaultFen };
	}

	var fromCol	= 12 - from % 16;
	var toCol	= 12 - to   % 16;
	var piece   = situation[from] & 15;
	var result	= "";

	// 相象仕士
	if (piece === 3 || piece === 4) {
		result = vschess.n2f[piece | 16] + fromCol;
	}
	// 兵卒
	else if (piece === 7) {
		for (var i = 60 - fromCol, pLength = 0; i < 204; i += 16) {
			situation[i] === situation[from] && ++pLength;
		}

		if (pLength === 1) {
			result = "P" + fromCol;
		}
		else {
			for (var i = 59, pList = []; i > 50; --i) {
				for (var j = i, pColList = []; j < 204; j += 16) {
					situation[j] === situation[from] && pColList.push(j);
				}

				pColList.length > 1 && (pList = pList.concat(pColList));
			}

			if (pList.length === 2) {
				result = "P" + "+-" .charAt(pList.indexOf(from));
			}
			else if (pList.length === 3) {
				result = "P" + "+.-".charAt(pList.indexOf(from));
			}
			else {
				result = "P" + vschess.fcc(pList.indexOf(from) + 97);
			}
		}
	}
	// 车马帅将炮
	else {
		for (var i = from + 16; i < 204 && !result; i += 16) {
			situation[i] === situation[from] && (result = vschess.n2f[piece | 16] + "+");
		}

		for (var i = from - 16; i >  50 && !result; i -= 16) {
			situation[i] === situation[from] && (result = vschess.n2f[piece | 16] + "-");
		}

		result || (result = vschess.n2f[piece | 16] + fromCol);
	}

	// 马相象仕士
	if (piece === 2 || piece === 3 || piece === 4) {
		result += (from > to ? "+" : "-") + toCol;
	}
	// 车帅将炮兵卒
	else {
		var offset = to - from;

		if (Math.abs(offset) > 15) {
			result += (offset > 0 ? "-" : "+") + Math.abs(offset >> 4);
		}
		else {
			result += "." + toCol;
		}
	}

	if (result) {
		situation[to  ]   = situation[from];
		situation[from]   = 1;
		situation[0   ]   = 3    - situation[0];
		situation[0   ] === 1 && ++situation[1];
		return { move: result, movedFen: isB ? vschess.roundFen(vschess.situationToFen(situation)) : vschess.situationToFen(situation) };
	}

	return { move: "None", movedFen: vschess.defaultFen };
};


// 检查指定局面号下指定位置是否为红方棋子
vschess.load.prototype.isR = function(index, step){
	step  = vschess.limit(step, 0, this.lastSituationIndex(), this.getCurrentStep());
	index = vschess.turn[this.getTurn()][vschess.limit(index, 0, 89)];
	return this.situationList[step][vschess.b2s[index]] >> 4 === 1;
};

// 检查指定局面号下指定位置是否为黑方棋子
vschess.load.prototype.isB = function(index, step){
	step  = vschess.limit(step, 0, this.lastSituationIndex(), this.getCurrentStep());
	index = vschess.turn[this.getTurn()][vschess.limit(index, 0, 89)];
	return this.situationList[step][vschess.b2s[index]] >> 4 === 2;
};

// 检查指定局面号下指定位置是否无棋子
vschess.load.prototype.isN = function(index, step){
	step  = vschess.limit(step, 0, this.lastSituationIndex(), this.getCurrentStep());
	index = vschess.turn[this.getTurn()][vschess.limit(index, 0, 89)];
	return this.situationList[step][vschess.b2s[index]] === 1;
};

// 检查指定局面号下指定位置是否为己方棋子
vschess.load.prototype.isPlayer = function(index, step){
	step  = vschess.limit(step, 0, this.lastSituationIndex(), this.getCurrentStep());
	index = vschess.turn[this.getTurn()][vschess.limit(index, 0, 89)];
	return this.situationList[step][vschess.b2s[index]] >> 4 === this.situationList[step][0];
};

// 检查指定局面号下指定位置是否为敌方棋子
vschess.load.prototype.isEnermy = function(index, step){
	step  = vschess.limit(step, 0, this.lastSituationIndex(), this.getCurrentStep());
	index = vschess.turn[this.getTurn()][vschess.limit(index, 0, 89)];
	return this.situationList[step][vschess.b2s[index]] >> 4 === 3 - this.situationList[step][0];
};

// 获取指定起始棋子的所有合法目标坐标
vschess.load.prototype.getLegalByStartPieceIndex = function(startIndex){
	startIndex = vschess.b2s[vschess.turn[this.getTurn()][vschess.limit(startIndex, 0, 89)]];
	var legalList = [];

	for (var i = 0; i < this.legalList.length; ++i) {
		var targetIndex = vschess.turn[this.getTurn()][vschess.s2b[this.legalList[i][1]]];
		this.legalList[i][0] === startIndex && legalList.push(targetIndex);
	}

	return legalList;
};

// 将棋盘上的棋子移除，-1 表示动画棋子
vschess.load.prototype.clearPiece = function(index){
	var className =  "vschess-piece-R vschess-piece-N vschess-piece-B vschess-piece-A vschess-piece-K vschess-piece-C vschess-piece-P";
	className	 += " vschess-piece-r vschess-piece-n vschess-piece-b vschess-piece-a vschess-piece-k vschess-piece-c vschess-piece-p";

	if (typeof index === "undefined") {
		this.piece.removeClass(className);
	}
	else if (~index) {
		this.piece.eq(vschess.limit(index, 0, 89)).removeClass(className);
	}
	else {
		this.animatePiece.removeClass(className);
	}

	return this;
};

// 将棋盘上的选择状态移除，-1 表示动画棋子
vschess.load.prototype.clearSelect = function(index){
	if (typeof index === "undefined") {
		this.piece.removeClass("vschess-piece-S vschess-piece-s");
		this.setCurrentSelect(-1);
	}
	else if (~index) {
		this.piece.eq(vschess.limit(index, 0, 89)).removeClass("vschess-piece-S vschess-piece-s");
	}
	else {
		this.animatePiece.removeClass("vschess-piece-S vschess-piece-s");
	}

	return this;
};

// 将棋盘上的棋子及选择状态移除，-1 表示动画棋子
vschess.load.prototype.clearBoard = function(index){
	this.clearPiece(index);
	this.clearSelect(index);
	return this;
};

// 创建棋谱注解区域
vschess.load.prototype.createComment = function(){
    var _this = this;
    this.commentTitle = $('<div class="vschess-tab-title vschess-tab-title-comment">' + this.options.tagName.comment + '</div>');
	this.commentArea = $('<div class="vschess-tab-body vschess-tab-body-comment"></div>');
	this.commentTextarea = $('<textarea class="vschess-tab-body-comment-textarea"></textarea>').appendTo(this.commentArea);
	this.tabArea.children(".vschess-tab-title-comment, .vschess-tab-body-comment").remove();
	this.tabArea.append(this.commentTitle);
	this.tabArea.append(this.commentArea );
	this.commentTitle.bind(this.options.click, function(){ _this.showTab("comment"); });
	this.commentTextarea.bind("change" , function( ){ _this.editCommentByStep(_this.commentTextarea.val()); });
	this.commentTextarea.bind("keydown", function(e){ e.ctrlKey && e.keyCode === 13 && _this.commentTextarea.blur(); });
	this.createCommentPlaceholder();
	return this;
};

// 根据局面号填充注释
vschess.load.prototype.setCommentByStep = function(step){
	step = vschess.limit(step, 0, this.lastSituationIndex(), this.getCurrentStep());
	this.commentTextarea.val(this.commentList[step]);
	vschess.placeholder || (this.commentList[step] ?  this.commentTextareaPlaceholder.hide() : this.commentTextareaPlaceholder.show());
	return this;
};

// 创建棋谱注解区域空白提示
vschess.load.prototype.createCommentPlaceholder = function(){
	if (vschess.placeholder) {
		this.commentTextarea.attr({ "placeholder": "这里可以填写注解" });
		return this;
	}

	var _this = this, commentMonitor;
	this.commentTextareaPlaceholder = $('<div class="vschess-tab-body-comment-textarea-placeholder">这里可以填写注解</div>');
	this.commentArea.append(this.commentTextareaPlaceholder);
	this.commentTextarea.bind("focus", function(){ commentMonitor = setInterval(function(){ _this.commentTextarea.val() ? _this.commentTextareaPlaceholder.hide() : _this.commentTextareaPlaceholder.show(); }, 20); });
	this.commentTextarea.bind("blur" , function(){ clearInterval(commentMonitor); });
	return this;
};

// 修改当前节点树下指定局面号的注解
vschess.load.prototype.editCommentByStep = function(comment, step){
	step = vschess.limit(step, 0, this.lastSituationIndex(), this.getCurrentStep());
	this.selectDefault(step).comment = comment;
	this.commentList[step] = comment;
	this.refreshMoveListNode();
	this.setCommentByStep();
	this.rebuildExportAll();
	this.setExportFormat();
	return this;
};

// 创建棋盘选项区域
vschess.load.prototype.createConfig = function(){
	var _this = this;
    this.configTitle = $('<div class="vschess-tab-title vschess-tab-title-config">' + this.options.tagName.config + '</div>');
	this.configArea  = $('<div class="vschess-tab-body vschess-tab-body-config"></div>');
	this.tabArea.children(".vschess-tab-title-config, .vschess-tab-body-config").remove();
	this.tabArea.append(this.configTitle);
	this.tabArea.append(this.configArea );
	this.configTitle.bind(this.options.click, function(){ _this.showTab("config"); });
	this.createConfigSwitch();
	return this;
};

// 创建棋盘选项开关列表
vschess.load.prototype.createConfigSwitch = function(){
	var _this = this;
	this.configSwitchList = $('<ul class="vschess-tab-body-config-list"></ul>');
	this.configArea.append(this.configSwitchList);
	this.configItem   = {};
	this.configItemM  = {};
	this.configValue  = {};
	this.configRange  = {};
	this.configSelect = {};

	this.addConfigItem("turnX", "左右翻转", "boolean", true, "", function(){
		_this.setTurn(_this.configValue["turnY"] * 2 + _this.configValue["turnX"], 1);
	});

	this.addConfigItem("turnY", "上下翻转", "boolean", true, "", function(){
		_this.setTurn(_this.configValue["turnY"] * 2 + _this.configValue["turnX"], 1);
	});

	this.addConfigItem("moveTips", "走子提示", "boolean", true, "", function(){
		_this._.moveTips = _this.configValue["moveTips"];
	});

	this.addConfigItem("sound", "走子音效", "boolean", true, "", function(){
		_this._.sound = _this.configValue["sound"];
	});

	this.addConfigItem("speakMove", "着法朗读", "boolean", false, "", function(){
		_this._.speakMove = _this.configValue["speakMove"];
	});

	this.addConfigItem("saveTips", "保存提示", "boolean", true, "", function(){
		_this._.saveTips = _this.configValue["saveTips"];
	});

	this.addConfigItem("pieceRotate", "棋子旋转", "boolean", true, "", function(){
		_this._.pieceRotate = _this.configValue["pieceRotate"];
		_this.setBoardByStep();
	});

	this.addConfigItem("banRepeatLongThreat", "禁止长打", "boolean", true, "", function(){
		_this._.banRepeatLongThreat = _this.configValue["banRepeatLongThreat"];
	});

	this.addConfigItem("banRepeatLongKill", "禁止一将一杀" , "boolean", true, "", function(){
		_this._.banRepeatLongKill = _this.configValue["banRepeatLongKill"];
		_this.repeatLongKillMoveList = _this._.banRepeatLongKill ? _this.getRepeatLongKillMove() : [];
	});

	this.addConfigItem("illegalTips", "违例提示", "boolean", true, "", function(){
		_this._.illegalTips = _this.configValue["illegalTips"];
	});

	this.addConfigItem("playGap", "播放间隔", "select" , 5, "0.1秒:1,0.2秒:2,0.5秒:5,1秒:10,2秒:20,5秒:50", function(){
		_this._.playGap = _this.configValue["playGap"];
	});

	this.addConfigItem("volume", "音效音量", "range", 100, "0,100", function(){
		_this._.volume = _this.configValue["volume"];
	});

	return this;
};

// 添加棋盘选项开关
vschess.load.prototype.addConfigItem = function(name, text, type, defaultValue, param, action){
	var _this = this;
	this.configItem [name] = $('<li class="vschess-tab-body-config-item vschess-tab-body-config-item-' + name + '">' + text + '</li>');
	this.configValue[name] = defaultValue;

	if (type === "boolean") {
		this.configItemM[name] = $('<div class="vschess-tab-body-config-item-boolean"><span></span></div>');
		this.configItemM[name].bind(this.options.click, function(){ _this.setConfigItemValue(name, !_this.configValue[name]); typeof action === "function" && action(); });
		this.configValue[name] || this.configItemM[name].addClass("vschess-tab-body-config-item-boolean-false");
	}
	else if (type === "select") {
		var selectList = param.split(",");
		this.configSelect[name] = { item: [] };
		this.configItemM [name] = $('<select class="vschess-tab-body-config-item-select"></select>');

		for (var i = 0; i < selectList.length; ++i) {
			var _name  = selectList[i].split(":")[0];
			var _value = selectList[i].split(":")[1];
			this.configSelect[name].item.push({ name: _name, value: _value });
			this.configItemM [name].append('<option value="' + _value + '">' + _name + '</option>');
		}

		this.configItemM[name].bind("change", function(){ _this.setConfigItemValue(name, this.value); typeof action === "function" && action(); });
	}
	else if (type === "range") {
		var min = +param.split(",")[0];
		var max = +param.split(",")[1];
		var startX = 0, drag = false;
		var k = (defaultValue - min) * 100 / (max - min);

		this.configItemM[name] = $('<div class="vschess-tab-body-config-item-range"></div>');
		this.configRange[name] = { bar: $('<div class="vschess-tab-body-config-item-range-bar"></div>'), k: k, min: min, max: max };
		this.configItemM[name].append(this.configRange[name].bar);
		this.configRange[name].bar.css({ left: k });

		this.configRange[name].bar.bind("mousedown touchstart", function(e){
			startX = e.type === "mousedown" ? e.pageX : e.touches[0].pageX;
			drag = true;
		});

		$(document).bind("mousemove touchmove", function(e){
			if (!drag) {
				return true;
			}

			var X = e.type === "mousemove" ? e.pageX : e.touches[0].pageX;
			var deltaX = X - startX;
			var K = _this.configRange[name].k + deltaX;
			K > 100 && (K = 100);
			K <   0 && (K =   0);
			_this.configRange[name].bar.css({ left: K });
			_this.setConfigItemValue(name, K);
			typeof action === "function" && action();
			return false;
		});

		$(document).bind("mouseup touchend", function(e){
			if (!drag) {
				return true;
			}

			var X = e.type === "mouseup" ? e.pageX : e.changedTouches[0].pageX;
			var deltaX = X - startX;
			var K = _this.configRange[name].k + deltaX;
			K > 100 && (K = 100);
			K <   0 && (K =   0);
			_this.configRange[name].k = K;
			_this.configRange[name].bar.css({ left: K });
			_this.setConfigItemValue(name, K);
			typeof action === "function" && action();
			drag = false;
		});
	}

	this.configItem [name].append(this.configItemM[name]);
	this.configSwitchList .append(this.configItem[name]);
	return this;
};

// 设置棋盘选项开关
vschess.load.prototype.setConfigItemValue = function(name, value){
	if (this.configRange[name]) {
		this.configValue[name] = this.configRange[name].min + (this.configRange[name].max - this.configRange[name].min) * value / 100;
		this.configRange[name].bar.css({ left: value });
	}
	else if (this.configSelect[name]) {
		this.configValue[name] = value;

		for (var i = 0; i < this.configSelect[name].item.length; ++i) {
			if ("" + this.configSelect[name].item[i].value === "" + value) {
				this.configItemM[name][0].selectedIndex = i;
				break;
			}
		}
	}
	else {
		this.configValue[name] = value;
		this.configValue[name] ? this.configItemM[name].removeClass("vschess-tab-body-config-item-boolean-false") : this.configItemM[name].addClass("vschess-tab-body-config-item-boolean-false");
	}

	return this;
};

// 播放控制器
vschess.load.prototype.createControlBar = function(){
	var _this = this;
	this.controlBar = $('<div class="vschess-control-bar"></div>');
	this.controlBarButton = {
		first: $('<button type="button" class="vschess-button vschess-control-bar-button vschess-control-bar-first">开 局</button>'),
		prevQ: $('<button type="button" class="vschess-button vschess-control-bar-button vschess-control-bar-prevQ">快 退</button>'),
		prev : $('<button type="button" class="vschess-button vschess-control-bar-button vschess-control-bar-prev" >后 退</button>'),
		play : $('<button type="button" class="vschess-button vschess-control-bar-button vschess-control-bar-play" >播 放</button>'),
		pause: $('<button type="button" class="vschess-button vschess-control-bar-button vschess-control-bar-pause">暂 停</button>'),
		next : $('<button type="button" class="vschess-button vschess-control-bar-button vschess-control-bar-next" >前 进</button>'),
		nextQ: $('<button type="button" class="vschess-button vschess-control-bar-button vschess-control-bar-nextQ">快 进</button>'),
		last : $('<button type="button" class="vschess-button vschess-control-bar-button vschess-control-bar-last" >终 局</button>')
	};

	this.controlBarButton.first.bind(this.options.click, function(){ _this.pause(false).setBoardByStep(0); });
	this.controlBarButton.last .bind(this.options.click, function(){ _this.pause(false).setBoardByStep(_this.lastSituationIndex()); });
	this.controlBarButton.prev .bind(this.options.click, function(){ _this.pause(false).setBoardByOffset(-1); });
	this.controlBarButton.next .bind(this.options.click, function(){ _this.pause(false).animateToNext(); });
	this.controlBarButton.prevQ.bind(this.options.click, function(){ _this.pause(false).setBoardByOffset(-_this.getQuickStepOffset()); });
	this.controlBarButton.nextQ.bind(this.options.click, function(){ _this.pause(false).setBoardByOffset( _this.getQuickStepOffset()); });
	this.controlBarButton.play .bind(this.options.click, function(){ _this.lastSituationIndex() && _this.play(); });
	this.controlBarButton.pause.bind(this.options.click, function(){ _this.pause(); });

	for (var i in this.controlBarButton) {
		this.controlBar.append(this.controlBarButton[i]);
	}

	this.controlBarButton.play.addClass("vschess-control-bar-button-current");
	this.DOM.append(this.controlBar);
	return this;
};

// 自动播放
vschess.load.prototype.play = function(){
	this.getCurrentStep() >= this.lastSituationIndex() && this.setBoardByStep(0);
	this.interval.time = this.getPlayGap();
	this.controlBarButton.play .removeClass("vschess-control-bar-button-current");
	this.controlBarButton.pause.   addClass("vschess-control-bar-button-current");
	return this;
};

// 暂停播放
vschess.load.prototype.pause = function(playSound){
	this.interval.time = 0;
	this.controlBarButton.pause.removeClass("vschess-control-bar-button-current");
	this.controlBarButton.play .   addClass("vschess-control-bar-button-current");
	this.animating && this.stopAnimate(playSound);
	return this;
};

// 格式控制器
vschess.load.prototype.createFormatBar = function(){
	var _this = this;
	this.formatBar = $('<form method="post" action="' + this.options.cloudApi.saveBook + '" class="vschess-format-bar"></form>');

	switch (this.getMoveFormat()) {
		case "chinese"	: var formarButton = "中 文"; break;
	}

	this.formatBarButton = {
		random		: $('<button type="button" class="vschess-button vschess-format-bar-button vschess-format-bar-format" >随 机</button>'),
		copy		: $('<button type="button" class="vschess-button vschess-format-bar-button vschess-format-bar-copy"   >复 制</button>'),
		help		: $('<button type="button" class="vschess-button vschess-format-bar-button vschess-format-bar-help"   >帮 助</button>'),
		save		: $('<button type="button" class="vschess-button vschess-format-bar-button vschess-format-bar-save"   >保 存</button>'),
		saveFormat	: $('<input  type="hidden" class="vschess-format-bar-save-format"   name="format" value="DhtmlXQ" />'),
		saveInput	: $('<input  type="hidden" class="vschess-format-bar-save-input"    name="data" />'),
		saveFilename: $('<input  type="hidden" class="vschess-format-bar-save-filename" name="filename" />')
	};

	this.formatBarButton.random.bind(this.options.click, function(){
        _this.randomReview();
	});

	this.formatBarButton.help.bind(this.options.click, function(){
		_this.showHelpArea();
	});

	this.formatBarButton.save.bind(this.options.click, function(){
		_this.rebuildExportDhtmlXQ();
		_this.setSaved(true);

		if (vschess.localDownload) {
			let UTF8Text = _this.exportData.DhtmlXQ.replace(/\n/g, "\r\n").replace(/\r\r/g, "\r");
            let title = (_this.chessInfo.title || '中国象棋') + ".txt";

            if (_this.loadingRedOpening) {
              UTF8Text = "const red_opening = `\n" + UTF8Text + "\n`;";
              title = "red_opening.txt";
            }

            if (_this.loadingBlackOpening) {
                UTF8Text = "const black_opening = `\n" + UTF8Text + "\n`;";
                title = "black_opening.txt";
            }

			_this.localDownload(title, UTF8Text, { type: "text/plain" });
		}
		else {
			_this.formatBarButton.saveInput   .val(_this.exportData.DhtmlXQ);
			_this.formatBarButton.saveFilename.val(_this.chessInfo .title  );
			_this.formatBar.trigger("submit");
		}
	});

	for (var i in this.formatBarButton) {
		this.formatBar.append(this.formatBarButton[i]);
	}

	this.formatBarButton.copy.bind(this.options.click, function(){
		_this.copy(_this.getCurrentFen(), function(){ _this.showMessage("局面复制成功，您可以直接在象棋软件中粘贴使用！"); });
	});

	this.DOM.append(this.formatBar);
	return this;
};

// 设置快进快退偏移量
vschess.load.prototype.setQuickStepOffset = function(quickStepOffset){
	this._.quickStepOffset = vschess.limit(quickStepOffset, 1, Infinity);
	this.refreshHelp();
	return this;
};

// 取得快进快退偏移量
vschess.load.prototype.getQuickStepOffset = function(){
	return this._.quickStepOffset;
};

// 设置自动播放时间间隔
vschess.load.prototype.setPlayGap = function(playGap){
	this._.playGap = vschess.limit(playGap, 1, Infinity);
	this.setConfigItemValue("playGap", this._.playGap);
	this.interval && this.interval.time && (this.interval.time = this.getPlayGap());
	return this;
};

// 取得自动播放时间间隔
vschess.load.prototype.getPlayGap = function(){
	return this._.playGap;
};

// 创建复制用文本框
vschess.load.prototype.createCopyTextarea = function(){
	this.copyTextarea = $('<textarea class="vschess-copy" readonly="readonly"></textarea>').appendTo(this.DOM);
	return this;
};

// 复制字符串
vschess.load.prototype.copy = function(str, success){
	typeof success !== "function" && (success = function(){});

	if (document.execCommand && document.queryCommandSupported && document.queryCommandSupported('copy')) {
		this.copyTextarea.val(str);
		this.copyTextarea[0].select();
		this.copyTextarea[0].setSelectionRange(0, str.length);

		if (document.execCommand("copy")) {
			success();
		}
		else {
			prompt("请按 Ctrl+C 复制：", str);
		}
	}
	else if (window.clipboardData) {
		if (window.clipboardData.setData("Text", str)) {
			success();
		}
		else {
			prompt("请按 Ctrl+C 复制：", str);
		}
	}
	else {
		prompt("请按 Ctrl+C 复制：", str);
	}

	return this;
};

// 创建信息提示框
vschess.load.prototype.createMessageBox = function(){
	this.messageBox = $('<div class="vschess-message-box"></div>');
	this.DOM.append(this.messageBox);
	return this;
};

// 显示提示框
vschess.load.prototype.showMessage = function(msg){
	var _this = this;
	this.messageBox.text(msg).addClass("vschess-message-box-show");
	setTimeout(function(){ _this.messageBox.removeClass("vschess-message-box-show"); }, 1500);
	return this;
};

// 取得当前节点树路径下局面数量
vschess.load.prototype.getSituationListLength = function(){
	return this.situationList ? this.situationList.length : 0;
};

// 取得当前节点树路径下最后局面的索引号
vschess.load.prototype.lastSituationIndex = function(){
	return this.situationList ? this.situationList.length - 1 : 0
};

// 取得当前节点树路径下的所有 Fen 串
vschess.load.prototype.getFenList = function(){
	if (!this.getTurnForMove()) {
		return this.fenList.slice(0);
	}

	var result = [];

	for (var i = 0; i < this.fenList.length; ++i) {
		result.push(vschess.turnFen(this.fenList[i]));
	}

	return result;
};

// 取得当前节点树路径下的所有节点 ICCS 着法，[0] 为初始 Fen 串
vschess.load.prototype.getMoveList = function(){
	if (!this.getTurnForMove()) {
		return this.moveList.slice(0);
	}

	var result = [];

	for (var i = 0; i < this.moveList.length; ++i) {
		if (i === 0) {
			result.push(vschess.turnFen(this.moveList[i]));
		}
		else {
			result.push(vschess.turnMove(this.moveList[i]));
		}
	}

	return result;
};

// 取得指定局面号 Fen 串
vschess.load.prototype.getFenByStep = function(step){
	return this.getFenList()[vschess.limit(step, 0, this.lastSituationIndex(), this.getCurrentStep())];
};

// 取得指定局面号节点 ICCS 着法，step 为 0 时返回初始 Fen 串
vschess.load.prototype.getMoveByStep = function(step){
	return this.moveList[vschess.limit(step, 0, this.lastSituationIndex(), this.getCurrentStep())];
};

// 取得当前 Fen 串
vschess.load.prototype.getCurrentFen = function(){
	return this.getFenByStep(this.getCurrentStep());
};

// 取得初始 Fen 串
vschess.load.prototype.getStartFen = function(){
	return this.getFenByStep(0);
};

// 取得当前节点 ICCS 着法，起始局面为初始 Fen 串
vschess.load.prototype.getCurrentMove = function(){
	return this.getMoveByStep(this.getCurrentStep());
};

// 取得指定局面号着法是否为吃子着法
vschess.load.prototype.getEatStatusByStep = function(step){
	return this.eatStatus[vschess.limit(step, 0, this.eatStatus.length - 1, this.getCurrentStep())];
};

// 取得 UCCI 着法列表
vschess.load.prototype.getUCCIList = function(step){
	step = vschess.limit(step, 0, this.eatStatus.length - 1, this.getCurrentStep());
	var startIndex = 0, result = [];

	for (var i = step; i >= 0 && !startIndex; --i) {
		this.eatStatus[i] && (startIndex = i);
	}

	result.push(this.getFenList()[startIndex]);
	result = result.concat(this.getMoveList().slice(startIndex + 1, step + 1));
	return result;
};

// 取得 UCCI 局面列表
vschess.load.prototype.getUCCIFenList = function(step){
	step = vschess.limit(step, 0, this.eatStatus.length - 1, this.getCurrentStep());
    var startIndex = 0;

	for (var i = step; i >= 0 && !startIndex; --i) {
		this.eatStatus[i] && (startIndex = i);
	}

	return this.getFenList().slice(startIndex, step + 1);
};

// 取得重复长打着法（棋规判负）
vschess.load.prototype.getRepeatLongThreatMove = function(){
	return vschess.repeatLongThreatMove(this.getUCCIList());
};

// 取得重复一将一杀着法（中国棋规判负）
vschess.load.prototype.getRepeatLongKillMove = function(){
	return vschess.repeatLongKillMove(this.getUCCIList());
};

// 根据局面号取得节点
vschess.load.prototype.getNodeByStep = function(step){
	step = vschess.limit(step, 0, this.eatStatus.length - 1, this.getCurrentStep());
	return this.nodeList[step];
};

// 创建编辑局面区域
vschess.load.prototype.createEdit = function(){
	var _this = this;
    this.editTitle = $('<div class="vschess-tab-title vschess-tab-title-edit">' + this.options.tagName.edit + '</div>');
	this.editArea  = $('<div class="vschess-tab-body vschess-tab-body-edit"></div>');
	this.tabArea.children(".vschess-tab-title-edit, .vschess-tab-body-edit").remove();
	this.tabArea.append(this.editTitle);
	this.tabArea.append(this.editArea );
	this.editTitle.bind(this.options.click, function(){ _this.showTab("edit"); });
	this.recommendStartList = this.options.recommendList;
	this.editNodeTextarea   = { val: function(){ return ""; } };
	this.createEditStartButton();
	this.createNodeStartButton();
	this.createEditOtherButton();
	this.showEditStartButton  ();

	if (this.options.cloudApi && this.options.cloudApi.startFen) {
		$.ajax({
			url: this.options.cloudApi.startFen,
			dataType: "jsonp",
			success: function(data){
				typeof data === "string" && (data = $.parseJSON(data));

				if (data.code === 0) {
					_this.recommendStartList = _this.options.recommendList.concat(data.data);
				}
				else {
				}

				typeof _this.callback_afterStartFen === "function" && _this.callback_afterStartFen();
			}
		});
	}

	return this;
};

// 创建编辑局面区域非即时加载组件
vschess.load.prototype.createEditOtherItem = function(){
	if (this._.fenEditorCreated) {
		return this;
	}

	this._.fenEditorCreated = true;
	this.createEditEndButton();
	this.createEditCancelButton();
	this.createEditTextarea();
	this.createEditPlaceholder();
	this.createEditPieceArea();
	this.createEditStartRound();
	this.createEditStartPlayer();
	this.createEditBoard();
	this.createRecommendList();
	this.createNodeEndButton();
	this.createNodeCancelButton();
	this.createNodeEditTextarea();
	this.createNodeEditPlaceholder();
	return this;
};

// 显示编辑开始按钮
vschess.load.prototype.showEditStartButton = function(){
	for (var i = 0; i < vschess.editStartList.length; ++i) {
		if (this[vschess.editStartList[i]] && typeof this[vschess.editStartList[i]].addClass === "function") {
			this[vschess.editStartList[i]].addClass("vschess-tab-body-edit-current");
		}
	}

	return this;
};

// 隐藏编辑开始按钮
vschess.load.prototype.hideEditStartButton = function(){
	for (var i = 0; i < vschess.editStartList.length; ++i) {
		if (this[vschess.editStartList[i]] && typeof this[vschess.editStartList[i]].removeClass === "function") {
			this[vschess.editStartList[i]].removeClass("vschess-tab-body-edit-current");
		}
	}

	return this;
};

// 显示编辑局面组件
vschess.load.prototype.showEditModule = function(){
	for (var i = 0; i < vschess.editModuleList.length; ++i) {
		if (this[vschess.editModuleList[i]] && typeof this[vschess.editModuleList[i]].addClass === "function") {
			this[vschess.editModuleList[i]].addClass("vschess-tab-body-edit-current");
		}
	}

    this.DOM.addClass("vschess-edit-mode");
	return this;
};

// 隐藏编辑局面组件
vschess.load.prototype.hideEditModule = function(){
	for (var i = 0; i < vschess.editModuleList.length; ++i) {
		if (this[vschess.editModuleList[i]] && typeof this[vschess.editModuleList[i]].removeClass === "function") {
			this[vschess.editModuleList[i]].removeClass("vschess-tab-body-edit-current");
		}
	}

    this.DOM.removeClass("vschess-edit-mode");
	return this;
};

// 显示粘贴棋谱组件
vschess.load.prototype.showNodeEditModule = function(){
	for (var i = 0; i < vschess.editNodeModuleList.length; ++i) {
		if (this[vschess.editNodeModuleList[i]] && typeof this[vschess.editNodeModuleList[i]].addClass === "function") {
			this[vschess.editNodeModuleList[i]].addClass("vschess-tab-body-edit-current");
		}
	}

	return this;
};

// 隐藏粘贴棋谱组件
vschess.load.prototype.hideNodeEditModule = function(){
	for (var i = 0; i < vschess.editNodeModuleList.length; ++i) {
		if (this[vschess.editNodeModuleList[i]] && typeof this[vschess.editNodeModuleList[i]].removeClass === "function") {
			this[vschess.editNodeModuleList[i]].removeClass("vschess-tab-body-edit-current");
		}
	}

	return this;
};

// 创建编辑局面区域开始编辑按钮
vschess.load.prototype.createEditStartButton = function(){
	var _this = this;
	this.editStartButton = $('<button type="button" class="vschess-button vschess-tab-body-edit-start-button">编辑局面</button>');
	this.editStartButton.appendTo(this.editArea);
	this.editStartButton.bind(this.options.click, function(){ _this.showEditBoard(); });
	return this;
};

// 显示编辑局面界面
vschess.load.prototype.showEditBoard = function(){
	this.showTab("edit");
	this.createEditOtherItem();
	this.pause(false);
	this.fillInRecommendList(0);
	this.hideEditStartButton();
	this.hideNodeEditModule();
	this.showEditModule();
	this.fillEditBoardByFen(this.getFenByStep(this.getCurrentStep()));
	this.fillInRecommendList(this.recommendClass[0].selectedIndex);
	this.editSelectedIndex = -99;
	this.dragPiece = null;
	return this;
};

// 创建编辑局面区域结束编辑按钮
vschess.load.prototype.createEditEndButton = function(){
	var _this = this;
	this.editEndButton = $('<button type="button" class="vschess-button vschess-tab-body-edit-end-button">确 定</button>');
	this.editEndButton.appendTo(this.editArea);

	this.editEndButton.bind(this.options.click, function(){
		if (!_this.confirm("确定使用新的局面吗？当前棋谱会丢失！")) {
			return false;
		}

		var fen				= vschess.situationToFen(_this.editSituation);
		var fenRound		= vschess.roundFen(fen);
		var errorList		= vschess.checkFen(fen);
		var errorListRound	= vschess.checkFen(fenRound);
		var turn = 0;

		if (errorList.length > errorListRound.length) {
			errorList = errorListRound;
			fen = fenRound;
			turn = 3;
		}

		if (errorList.length > 1) {
			var errorMsg = ["当前局面出现下列错误：\n"];

			for (var i = 0; i < errorList.length; ++i) {
				errorMsg.push(i + 1, ".", errorList[i], i === errorList.length - 1 ? "。" : "；\n");
			}

			alert(errorMsg.join(""));
		}
		else if (errorList.length > 0) {
			alert(errorList[0] + "。");
		}
		else {
			_this.hideNodeEditModule();
			_this.hideEditModule();
			_this.showEditStartButton();
			_this.editTextarea.val("");
			_this.setNode({ fen: fen, comment: "", next: [], defaultIndex: 0 });
			_this.rebuildSituation();
			_this.setBoardByStep(0);
			_this.refreshMoveSelectListNode();
			_this.chessInfo = {};
			_this.insertInfoByCurrent();
			_this.refreshInfoEditor();
			_this.rebuildExportAll();
			_this.setExportFormat();
			_this.setTurn(turn);
			_this.setSaved(true);

            _this.loadingRedOpening = false;
            _this.loadingBlackOpening = false;
            _this.setChessTitle(this.chessInfo && this.chessInfo.title || "中国象棋");
		}
	});

	return this;
};

// 创建编辑局面区域取消编辑按钮
vschess.load.prototype.createEditCancelButton = function(){
	var _this = this;
	this.editCancelButton = $('<button type="button" class="vschess-button vschess-tab-body-edit-cancel-button">取 消</button>');
	this.editCancelButton.appendTo(this.editArea);

	this.editCancelButton.bind(this.options.click, function(){
		_this.hideNodeEditModule();
		_this.hideEditModule();
		_this.showEditStartButton();
	});

	return this;
};

// 创建编辑局面区域输入框
vschess.load.prototype.createEditTextarea = function(){
	var _this = this;
	var UA = navigator.userAgent.toLowerCase(), contextMenu = "长按";
	!~UA.indexOf("android") && !~UA.indexOf("iph") && !~UA.indexOf("ipad") && (contextMenu = "右键单击");
	this.editTipsText = "点击右侧的棋子可将其放置在棋盘上，" + contextMenu + "棋盘上的棋子可以将其移除。";
	this.editTips = $('<input class="vschess-tab-body-edit-tips" value="' + this.editTipsText + '" readonly="readonly" />').appendTo(this.DOM);
	this.editTextarea = $('<textarea class="vschess-tab-body-edit-textarea"></textarea>').appendTo(this.editArea);

	this.editTextarea.bind("change" , function(){
		_this.fillEditBoardByText($(this).val());
		var currentFen = vschess.situationToFen(_this.editSituation);
		_this.editTips.val(currentFen.split(" ")[0] === vschess.blankFen.split(" ")[0] ? _this.editTipsText : currentFen);
	});

	this.editTextarea.bind("keydown", function(e){ e.ctrlKey && e.keyCode === 13 && _this.editTextarea.blur(); });
	return this;
};

// 创建编辑局面区域空白提示
vschess.load.prototype.createEditPlaceholder = function(){
	var placeholderText = "请将局面代码粘贴到这里，支持标准FEN、东萍象棋、象棋世家等格式，其他格式程序会尝试进行识别。";

	if (vschess.placeholder) {
		this.editTextarea.attr({ "placeholder": placeholderText });
		this.editTextareaPlaceholder = $();
		return this;
	}

	var _this = this, editMonitor;
	this.editTextareaPlaceholder = $('<div class="vschess-tab-body-edit-textarea-placeholder">' + placeholderText + "</div>");
	this.editArea.append(this.editTextareaPlaceholder);
	this.editTextarea.bind("focus", function(){ editMonitor = setInterval(function(){ _this.editTextarea.val() ? _this.editTextareaPlaceholder.hide() : _this.editTextareaPlaceholder.show(); }, 20); });
	this.editTextarea.bind("blur" , function(){ clearInterval(editMonitor); });
	return this;
};

// 创建编辑局面区域棋子容器
vschess.load.prototype.createEditPieceArea = function(){
	var _this = this;
	var editPieceNameList = "RNBAKCP rnbakcp*";
	this.editPieceArea = $('<div class="vschess-tab-body-edit-area"></div>');
	this.editArea.append(this.editPieceArea);
	this.editPieceList = {};

	for (var i = 0; i < editPieceNameList.length; ++i) {
		var k = editPieceNameList.charAt(i);

		if (k === " ") {
			this.editPieceArea.append('<div class="vschess-piece-disabled"></div>');
		}
		else if (k === "*") {
			this.editPieceList[k] = $('<div class="vschess-piece vschess-piece-X" draggable="true"><span></span></div>');
			this.editPieceList[k].appendTo(this.editPieceArea);
		}
		else {
			this.editPieceList[k] = $('<div class="vschess-piece vschess-piece-' + k + '" draggable="true"><span></span></div>');
			this.editPieceList[k].appendTo(this.editPieceArea);
		}
	}

	this.editPieceArea.bind("dragover", function(e){
		e.preventDefault();
		return true;
	});

	this.editPieceArea.bind("drop", function(e){
		_this.editRemovePiece(_this.dragPiece);
		_this.fillEditBoard();
		var currentFen = vschess.situationToFen(_this.editSituation);
		_this.editTips.val(currentFen.split(" ")[0] === vschess.blankFen.split(" ")[0] ? _this.editTipsText : currentFen);
	});

	$.each(this.editPieceList, function(i){
		var currentIndex = -vschess.f2n[i];

		this.bind(_this.options.click, function(e){
			_this.editRemoveSelect();

			if (_this.editSelectedIndex === -99) {
				$(this).addClass("vschess-piece-s");
				_this.editSelectedIndex = currentIndex;
			}
			else {
				if (_this.editSelectedIndex === currentIndex) {
					_this.editSelectedIndex = -99;
				}
				else {
					$(this).addClass("vschess-piece-s");
					_this.editSelectedIndex = currentIndex;
				}
			}
		});

		this.bind("selectstart", function(e) {
			e.preventDefault();
			return false;
		});

		this.bind("dragstart", function(e){
			e.dataTransfer.setData("text", e.target.innerHTML);
			_this.dragPiece = currentIndex;
			_this.editRemoveSelect();
			_this.editSelectedIndex = -99;
		});

		this.bind("drop", function(e) {
			e.stopPropagation();
			e.preventDefault();
			_this.editRemovePiece(_this.dragPiece);
			_this.fillEditBoard();
			var currentFen = vschess.situationToFen(_this.editSituation);
			_this.editTips.val(currentFen.split(" ")[0] === vschess.blankFen.split(" ")[0] ? _this.editTipsText : currentFen);
			return false;
		});
	});

	return this;
};

// 创建编辑局面区域开始回合数编辑框
vschess.load.prototype.createEditStartRound = function(){
	var _this = this;
	this.editEditStartText = $('<div class="vschess-tab-body-edit-start-text">回合：</div>');
	this.editEditStartText.appendTo(this.editArea);
	this.editEditStartRound = $('<input type="number" class="vschess-tab-body-edit-start-round" />');
	this.editEditStartRound.appendTo(this.editArea);

	this.editEditStartRound.bind("change", function(){
		_this.editSituation[1] = vschess.limit($(this).val(), 1, Infinity, 1);
		_this.fillEditBoard();
		var currentFen = vschess.situationToFen(_this.editSituation);
		_this.editTips.val(currentFen.split(" ")[0] === vschess.blankFen.split(" ")[0] ? _this.editTipsText : currentFen);
	});

	return this;
};

// 创建编辑局面区域先行走子方选项
vschess.load.prototype.createEditStartPlayer = function(){
	var _this = this;
	this.editEditStartPlayer = $('<div class="vschess-tab-body-edit-start-player"><span></span></div>');
	this.editEditStartPlayer.appendTo(this.editArea);

	this.editEditStartPlayer.bind(this.options.click, function(){
		_this.editSituation[0] = 3 - _this.editSituation[0];
		_this.fillEditBoard();
		var currentFen = vschess.situationToFen(_this.editSituation);
		_this.editTips.val(currentFen.split(" ")[0] === vschess.blankFen.split(" ")[0] ? _this.editTipsText : currentFen);
	});

	return this;
};

// 创建编辑局面专用棋盘
vschess.load.prototype.createEditBoard = function(){
	var _this = this;
	this.editBoard = $('<div class="vschess-board-edit"></div>');
	this.DOM.append(this.editBoard);
	this.editBoard.append(new Array(91).join('<div class="vschess-piece"><span></span></div>'));
	this.editPiece = this.editBoard.children(".vschess-piece");

	this.editPiece.each(function(i){
		$(this).bind(_this.options.click, function(){
			_this.editRemoveSelect();

			if (_this.editSelectedIndex === -99) {
				if (_this.editSituation[vschess.b2s[i]] > 1) {
					_this.editSelectedIndex = i;
					$(this).addClass("vschess-piece-s");
				}
			}
			else {
				_this.editSelectedIndex === i || _this.editMovePiece(_this.editSelectedIndex, i);
				_this.editSelectedIndex = -99;
			}

			_this.fillEditBoard(true);
			var currentFen = vschess.situationToFen(_this.editSituation);
			_this.editTips.val(currentFen.split(" ")[0] === vschess.blankFen.split(" ")[0] ? _this.editTipsText : currentFen);
		});

		$(this).bind("contextmenu", function(e){
			e.preventDefault();
			_this.editRemovePiece(i);
			_this.fillEditBoard();
			var currentFen = vschess.situationToFen(_this.editSituation);
			_this.editTips.val(currentFen.split(" ")[0] === vschess.blankFen.split(" ")[0] ? _this.editTipsText : currentFen);
			return false;
		});

		$(this).bind("selectstart", function(e) {
			e.preventDefault();
			return false;
		});

		$(this).bind("dragstart", function(e){
			e.dataTransfer.setData("text", e.target.innerHTML);
			_this.dragPiece = i;
			_this.editRemoveSelect();
			_this.editSelectedIndex = -99;
		});

		$(this).bind("dragover", function(e){
			e.preventDefault();
			return true;
		});

		$(this).bind("drop", function(e){
			e.stopPropagation();
			e.preventDefault();

			if (_this.dragPiece !== i) {
				if (e.ctrlKey) {
					_this.editSituation[vschess.b2s[i]] = _this.editSituation[vschess.b2s[_this.dragPiece]];
				}
				else {
					_this.editMovePiece(_this.dragPiece, i);
				}
			}

			_this.fillEditBoard();
			var currentFen = vschess.situationToFen(_this.editSituation);
			_this.editTips.val(currentFen.split(" ")[0] === vschess.blankFen.split(" ")[0] ? _this.editTipsText : currentFen);
		});
	});

	return this;
};

// 编辑器移动一枚棋子
vschess.load.prototype.editMovePiece = function(from, to){
	if (from >= 0) {
		this.editSituation[vschess.b2s[to]] = this.editSituation[vschess.b2s[from]];
		this.editRemovePiece(from);
	}
	else if (from > -99) {
		this.editSituation[vschess.b2s[to]] = -from;
	}

	return this;
};

// 编辑器移除一枚棋子
vschess.load.prototype.editRemovePiece = function(i){
	i >= 0 && (this.editSituation[vschess.b2s[i]] = 1);
	return this;
};

// 编辑器移除选中状态
vschess.load.prototype.editRemoveSelect = function(){
	$.each(this.editPieceList, function(){ $(this).removeClass("vschess-piece-s"); });
	this.editPiece.removeClass("vschess-piece-s");
	return this;
};

// 创建推荐开局列表（云服务）
vschess.load.prototype.createRecommendList = function(){
	var _this = this;
	this.recommendClass = $('<select class="vschess-recommend-class"></select>');
	this.recommendList  = $('<ul class="vschess-recommend-list"></ul>');
	this.DOM.append(this.recommendClass);
	this.DOM.append(this.recommendList );
	this.recommendClass.bind("change", function(){ _this.fillInRecommendList(this.selectedIndex); });
	this.fillInRecommendClass();
	return this;
};

// 填充推荐开局分类列表
vschess.load.prototype.fillInRecommendClass = function(){
	this.recommendStartClassItem = [];

	for (var i = 0; i < this.recommendStartList.length; ++i) {
		var classItem = $(['<option value="', i, '">', this.recommendStartList[i].name, '</option>'].join("")).appendTo(this.recommendClass);
		this.recommendStartClassItem.push(classItem);
	}

	return this;
};

// 填充推荐开局列表
vschess.load.prototype.fillInRecommendList = function(classId){
	var _this = this;
	this.recommendList.empty();
	var list = this.recommendStartList[classId].fenList;

	for (var i = 0; i < list.length; ++i) {
		var recommendStart = $(['<li class="vschess-recommend-list-fen" data-fen="', list[i].fen, '"><span>', i + 1, '.</span>', list[i].name, '</li>'].join(""));
		this.recommendList.append(recommendStart);

		recommendStart.bind(this.options.click, function(){
			var fen = $(this).data("fen");
			_this.fillEditBoardByFen(fen);
			_this.editTips.val(fen.split(" ")[0] === vschess.blankFen.split(" ")[0] ? _this.editTipsText : fen);
		});
	}

	return this;
};

// 尝试识别文本棋谱
vschess.load.prototype.fillEditBoardByText = function(chessData){
	var RegExp = vschess.RegExp(), RegExp_Match, fen = vschess.blankFen;

	if (~chessData.indexOf("[DhtmlXQ]")) {
		fen = vschess.dataToNode_DhtmlXQ(chessData, true);
	}
	else if (RegExp_Match = RegExp.FenLong.exec(chessData)) {
		fen = RegExp_Match[0];
	}
	else if (RegExp_Match = RegExp.FenShort.exec(chessData)) {
		fen = RegExp_Match[0] + " - - 0 1";
	}
	else if (RegExp_Match = RegExp.FenMini.exec(chessData)) {
		fen = RegExp_Match[0] + " w - - 0 1";
	}

	return this.fillEditBoardByFen(fen);
};

// 将 Fen 串导入局面编辑区
vschess.load.prototype.fillEditBoardByFen = function(fen){
	(this.getTurn() >> 1) && (fen = vschess.roundFen(fen));
	this.editSituation = vschess.fenToSituation(fen);
	this.fillEditBoard();
	return this;
};

// 将当前编辑局面展示到视图中
vschess.load.prototype.fillEditBoard = function(ignoreSelect){
	var selected = this.editPiece.filter(".vschess-piece-s");
	this.editPiece.removeClass().addClass("vschess-piece").removeAttr("draggable");
	ignoreSelect && selected.addClass("vschess-piece-s");
	this.editEditStartRound.val(this.editSituation[1]);
	this.editEditStartPlayer.removeClass("vschess-tab-body-edit-start-player-black");
	this.editSituation[0] === 2 && this.editEditStartPlayer.addClass("vschess-tab-body-edit-start-player-black");

	for (var i = 51; i < 204; ++i) {
		this.editSituation[i] > 1 && this.editPiece.eq(vschess.s2b[i]).addClass("vschess-piece-" + vschess.n2f[this.editSituation[i]]).attr({ draggable: true });
	}

	return this;
};

// 创建粘贴棋谱区域开始编辑按钮
vschess.load.prototype.createNodeStartButton = function(){
	var _this = this;
	this.editNodeStartButton = $('<button type="button" class="vschess-button vschess-tab-body-edit-node-start-button">粘贴棋谱</button>');
	this.editNodeStartButton.appendTo(this.editArea);

	this.editNodeStartButton.bind(this.options.click, function(){
		_this.createEditOtherItem();
		_this.pause(false);
		_this.hideEditModule();
		_this.hideEditStartButton();
		_this.showNodeEditModule();
	});

	return this;
};

// 创建粘贴棋谱区域完成编辑按钮
vschess.load.prototype.createNodeEndButton = function(){
	var _this = this;
	this.editNodeEndButton = $('<button type="button" class="vschess-button vschess-tab-body-edit-node-end-button">确 定</button>');
	this.editNodeEndButton.appendTo(this.editArea);

	this.editNodeEndButton.bind(this.options.click, function(){
		if (!_this.confirm("确定使用新的棋谱吗？当前棋谱会丢失！")) {
			return false;
		}

		var chessData = _this.editNodeTextarea.val();
		_this.editNodeTextarea.val("");
		_this.setBoardByStep(0);
		_this.setNode(vschess.dataToNode(chessData));
		_this.rebuildSituation().refreshMoveSelectListNode().setBoardByStep(0);
		_this.chessInfo = vschess.dataToInfo(chessData);
		_this.insertInfoByCurrent();
		_this.refreshInfoEditor();
		_this.rebuildExportAll();
		_this.setExportFormat();
		_this.hideNodeEditModule();
		_this.hideEditModule();
		_this.showEditStartButton();
		_this.setSaved(true);

        _this.loadingRedOpening = false;
        _this.loadingBlackOpening = false;
        _this.setChessTitle(this.chessInfo && this.chessInfo.title || "中国象棋");
	});

	return this;
};

// 创建粘贴棋谱区域取消编辑按钮
vschess.load.prototype.createNodeCancelButton = function(){
	var _this = this;
	this.editNodeCancelButton = $('<button type="button" class="vschess-button vschess-tab-body-edit-node-cancel-button">取 消</button>');
	this.editNodeCancelButton.appendTo(this.editArea);

	this.editNodeCancelButton.bind(this.options.click, function(){
		_this.hideNodeEditModule();
		_this.hideEditModule();
		_this.showEditStartButton();
	});

	return this;
};

// 创建粘贴棋谱区域输入框
vschess.load.prototype.createNodeEditTextarea = function(){
	var _this = this;
	this.editNodeTextarea = $('<textarea class="vschess-tab-body-edit-node-textarea"></textarea>').appendTo(this.editArea);
	this.editNodeTextarea.bind("keydown", function(e){ e.ctrlKey && e.keyCode === 13 && _this.editNodeTextarea.blur(); });
	return this;
};

// 创建粘贴棋谱区域空白提示
vschess.load.prototype.createNodeEditPlaceholder = function(){
	var placeholderText = "请将棋谱代码粘贴到这里，或者直接将棋谱文件拖拽到棋盘上。支持标准PGN、东萍象棋 DhtmlXQ、鹏飞象棋 PFC、象棋世家、QQ 新中国象棋等格式，其他格式程序会尝试进行识别。";

	if (vschess.placeholder) {
		this.editNodeTextarea.attr({ "placeholder": placeholderText });
		this.editNodeTextareaPlaceholder = $();
		return this;
	}

	var _this = this, editMonitor;
	this.editNodeTextareaPlaceholder = $('<div class="vschess-tab-body-edit-node-textarea-placeholder">' + placeholderText + "</div>");
	this.editArea.append(this.editNodeTextareaPlaceholder);
	this.editNodeTextarea.bind("focus", function(){ editMonitor = setInterval(function(){ _this.editNodeTextarea.val() ? _this.editNodeTextareaPlaceholder.hide() : _this.editNodeTextareaPlaceholder.show(); }, 20); });
	this.editNodeTextarea.bind("blur" , function(){ clearInterval(editMonitor); });
	return this;
};

// 创建其他按钮
vschess.load.prototype.createEditOtherButton = function(){
	var _this = this;

	// 打开棋谱按钮
	var buttonId = "vschess-tab-body-edit-open-button-" + vschess.guid();
	this.editOpenButton = $('<label for="' + buttonId + '" class="vschess-button vschess-tab-body-edit-open-button">打开棋谱</label>');
	this.editOpenButton.appendTo(this.editArea);
	this.editOpenFile = $('<input type="file" class="vschess-tab-body-edit-open-file" id="' + buttonId + '" />');
	this.editOpenFile.appendTo(this.editArea);
	this.editOpenFile.bind("change", function(){
		if (typeof FileReader === "function") {
			if (this.files.length) {
				var file = this.files[0];
				var ext = file.name.split(".").pop().toLowerCase();
				var reader = new FileReader();
				reader.readAsArrayBuffer(file);
				reader.onload = function(){
					if (!_this.confirm("确定打开该棋谱吗？当前棋谱会丢失！")) {
						return false;
					}

					var RegExp    = vschess.RegExp();
					var fileData  = new Uint8Array(this.result);
					var chessData = vschess.join(fileData);

					if (~vschess.binaryExt.indexOf(ext)) {
						var chessNode = vschess.binaryToNode(fileData);
						var chessInfo = vschess.binaryToInfo(fileData);
					}
					else {
						(chessData = vschess.iconv2UTF8(fileData));
						var chessNode = vschess.dataToNode(chessData);
						var chessInfo = vschess.dataToInfo(chessData);
					}

					_this.setBoardByStep(0);
					_this.setNode(chessNode);
					_this.rebuildSituation();
					_this.refreshMoveSelectListNode();
					_this.setBoardByStep(0);
					_this.chessInfo = chessInfo;
					_this.insertInfoByCurrent();
					_this.refreshInfoEditor();
					_this.rebuildExportAll();
					_this.setExportFormat();
					_this.editNodeTextarea.val("");
					_this.hideNodeEditModule();
					_this.hideEditModule();
					_this.showEditStartButton();
					_this.setSaved(true);

                    _this.loadingRedOpening = false;
                    _this.loadingBlackOpening = false;
                    _this.setChessTitle(this.chessInfo && this.chessInfo.title || "中国象棋");
				}
			}
		}
		else {
			alert("对不起，该浏览器不支持打开棋谱。");
		}

		this.value = "";
	});

	// 重新开局按钮
	this.editBeginButton = $('<button type="button" class="vschess-button vschess-tab-body-edit-begin-button">重新开局</button>');
	this.editBeginButton.appendTo(this.editArea);

	this.editBeginButton.bind(this.options.click, function(){
		if (!_this.confirm("确定重新开局吗？当前棋谱会丢失！")) {
			return false;
		}

		_this.setNode({ fen: vschess.defaultFen, comment: "", next: [], defaultIndex: 0 });
		_this.rebuildSituation();
        _this.setBoardByStep(0);
		_this.refreshMoveSelectListNode();
		_this.chessInfo = {};
		_this.insertInfoByCurrent();
		_this.refreshInfoEditor();
		_this.rebuildExportAll();
		_this.setExportFormat();
		_this.setTurn(0);
		_this.setSaved(true);

        _this.loadingRedOpening = false;
        _this.loadingBlackOpening = false;
        _this.setChessTitle(this.chessInfo && this.chessInfo.title || "中国象棋");
	});

	// 清空棋盘按钮
	this.editBlankButton = $('<button type="button" class="vschess-button vschess-tab-body-edit-blank-button">清空棋盘</button>');
	this.editBlankButton.appendTo(this.editArea);

	this.editBlankButton.bind(this.options.click, function(){
		_this.createEditOtherItem();
		_this.pause(false);
		_this.fillInRecommendList(0);
		_this.hideEditStartButton();
		_this.hideNodeEditModule();
		_this.showEditModule();
		_this.fillEditBoardByFen(vschess.blankFen);
		_this.editSelectedIndex = -99;
		_this.dragPiece = null;
	});

	// 随机复习按钮
	this.editRandomReviewButton = $('<button type="button" class="vschess-button vschess-tab-body-edit-begin-button">随机复习</button>');
	this.editRandomReviewButton.appendTo(this.editArea);
	this.editRandomReviewButton.bind(this.options.click, function(){ _this.randomReview(); });

    function loadOpening(chessData) {
      const chessNode = vschess.dataToNode(chessData);
      const chessInfo = vschess.dataToInfo(chessData);
      _this.setBoardByStep(0);
      _this.setNode(chessNode);
      _this.rebuildSituation();
      _this.refreshMoveSelectListNode();
      _this.setBoardByStep(0);
      _this.chessInfo = chessInfo;
      _this.insertInfoByCurrent();
      _this.refreshInfoEditor();
      _this.rebuildExportAll();
      _this.setExportFormat();
      _this.editNodeTextarea.val("");
      _this.hideNodeEditModule();
      _this.hideEditModule();
      _this.showEditStartButton();
      _this.setSaved(true);
    }

	this.editRedOpeningButton = $('<button type="button" class="vschess-button vschess-tab-body-edit-begin-button">红方开局库</button>');
	this.editRedOpeningButton.appendTo(this.editArea);
	this.editRedOpeningButton.bind(this.options.click, function(){
        if (_this.options.red_opening) {
            loadOpening(_this.options.red_opening);
            _this.setTurn(0);
            _this.loadingRedOpening = true;
            _this.loadingBlackOpening = false;
            _this.setChessTitle('红方开局库');
        } else {
            alert("红方开局库未开启");
        }
	});

	this.editBlackOpeningButton = $('<button type="button" class="vschess-button vschess-tab-body-edit-begin-button">黑方开局库</button>');
	this.editBlackOpeningButton.appendTo(this.editArea);
	this.editBlackOpeningButton.bind(this.options.click, function(){
        if (_this.options.black_opening) {
            loadOpening(_this.options.black_opening);
            _this.setTurn(3);
            _this.loadingRedOpening = false;
            _this.loadingBlackOpening = true;
            _this.setChessTitle('黑方开局库');
        } else {
            alert("黑方开局库未开启");
        }
	});
	return this;
};

// 绑定拖拽棋谱事件
vschess.load.prototype.bindDrag = function(){
	var _this = this;

	this.DOM.bind("dragover", function(e){
		e.preventDefault();
	});

	this.DOM.bind("drop", function(e){
		e.preventDefault();

		if (e.dataTransfer && e.dataTransfer.files.length) {
			var file = e.dataTransfer.files[0];
			var ext = file.name.split(".").pop().toLowerCase();
			var reader = new FileReader();
			reader.readAsArrayBuffer(file);
			reader.onload = function(){
				if (!_this.confirm("确定使用新的棋谱吗？当前棋谱会丢失！")) {
					return false;
				}

				var RegExp    = vschess.RegExp();
				var fileData  = new Uint8Array(this.result);
				var chessData = vschess.join(fileData);

				if (~vschess.binaryExt.indexOf(ext)) {
					var chessNode = vschess.binaryToNode(fileData);
					var chessInfo = vschess.binaryToInfo(fileData);
				}
				else {
					(chessData = vschess.iconv2UTF8(fileData));
					var chessNode = vschess.dataToNode(chessData);
					var chessInfo = vschess.dataToInfo(chessData);
				}

				_this.setBoardByStep(0);
				_this.setNode(chessNode);
				_this.rebuildSituation();
				_this.refreshMoveSelectListNode();
				_this.setBoardByStep(0);
				_this.chessInfo = chessInfo;
				_this.insertInfoByCurrent();
				_this.refreshInfoEditor();
				_this.rebuildExportAll();
				_this.setExportFormat();
				_this.editNodeTextarea.val("");
				_this.hideNodeEditModule();
				_this.hideEditModule();
				_this.showEditStartButton();
				_this.setSaved(true);
				_this.hideHelpArea();
				_this.hideInfoEditor();

                _this.loadingRedOpening = false;
                _this.loadingBlackOpening = false;
            _this.setChessTitle(this.chessInfo && this.chessInfo.title || "中国象棋");
			}
		}
	});

	return this;
};

// 确认提示框
vschess.load.prototype.confirm = function(str){
	if (this.getSaveTips() && !this.getSaved()) {
		return confirm(str);
	}
	else {
		return true;
	}
};

// 设置保存状态
vschess.load.prototype.setSaved = function(status){
	this._.saved = !!status;
	return this;
};

// 取得保存状态
vschess.load.prototype.getSaved = function(){
	return this._.saved;
};

// 设置保存提示状态
vschess.load.prototype.setSaveTips = function(status){
	this._.saveTips = !!status;
	this.setConfigItemValue("saveTips", this._.saveTips);
	return this;
};

// 取得保存提示状态
vschess.load.prototype.getSaveTips = function(){
	return this._.saveTips;
};

// 创建导出棋谱区域
vschess.load.prototype.createExport = function(){
	var _this = this;
    this.exportTitle = $('<div class="vschess-tab-title vschess-tab-title-export">' + this.options.tagName.export + '</div>');
	this.exportArea     = $('<form method="post" action="' + this.options.cloudApi.saveBook + '" class="vschess-tab-body vschess-tab-body-export"></form>');
	this.exportTextarea = $('<textarea class="vschess-tab-body-export-textarea" readonly="readonly" name="data"></textarea>').appendTo(this.exportArea);
	this.exportFormat   = $('<select class="vschess-tab-body-export-format"   name="format"></select>').appendTo(this.exportArea);
	this.exportFilename = $('<input  class="vschess-tab-body-export-filename" name="filename" type="hidden" />').appendTo(this.exportArea);
	this.exportGenerate = $('<button type="button" class="vschess-button vschess-tab-body-export-generate">生成棋谱</button>').appendTo(this.exportArea);
	this.exportCopy     = $('<button type="button" class="vschess-button vschess-tab-body-export-copy     vschess-tab-body-export-current">复制</button>').appendTo(this.exportArea);
	this.exportDownload = $('<button type="button" class="vschess-button vschess-tab-body-export-download vschess-tab-body-export-current">保存</button>').appendTo(this.exportArea);
	this.exportData     = {};
	this.tabArea.children(".vschess-tab-title-export, .vschess-tab-body-export").remove();
	this.tabArea.append(this.exportTitle);
	this.tabArea.append(this.exportArea );
	this.exportTitle.bind(this.options.click, function(){ _this.showTab("export"); });
	this.createExportList();
	return this;
};

// 创建导出格式列表
vschess.load.prototype.createExportList = function(){
	var _this = this, generating = false;
	this.exportFormatOptions = {};

	for (var i in vschess.exportFormatList) {
		this.exportFormatOptions[i] = $('<option value="' + i + '">' + vschess.exportFormatList[i] + '</option>');
		this.exportFormatOptions[i].addClass("vschess-tab-body-export-format-options");
		this.exportFormatOptions[i].addClass("vschess-tab-body-export-format-options-" + i);
		this.exportFormat.append(this.exportFormatOptions[i]);
	}

	this.exportFormat.bind("change", function(){
		if (_this.getNodeLength() >= vschess.bigBookCritical && (this.value === "DhtmlXQ")) {
			_this.exportDownload.removeClass("vschess-tab-body-export-current");
			_this.exportCopy    .removeClass("vschess-tab-body-export-current");
			_this.exportGenerate.   addClass("vschess-tab-body-export-current");
			_this.setExportFormat(this.value, "");
		}
		else {
			_this.exportGenerate.removeClass("vschess-tab-body-export-current");
			_this.exportCopy    .   addClass("vschess-tab-body-export-current");
			_this.exportDownload.   addClass("vschess-tab-body-export-current");
			_this.setExportFormat(this.value);
		}
	});

	this.exportGenerate.bind(this.options.click, function(){
		if (generating) {
			return false;
		}

		generating = true;
		_this.exportTextarea.val("正在生成棋谱，请稍候。");

		setTimeout(function(){

			_this.exportGenerate.removeClass("vschess-tab-body-export-current");
			_this.exportDownload.   addClass("vschess-tab-body-export-current");
			_this.exportCopy    .   addClass("vschess-tab-body-export-current");
			generating = false;
		}, vschess.threadTimeout);
	});

	this.exportCopy.bind(this.options.click, function(){
		_this.copy(_this.exportTextarea.val(), function(){ _this.showMessage("棋谱复制成功，您可以直接粘贴使用！"); });
	});

	this.exportDownload.bind(this.options.click, function(){
		if (vschess.localDownload) {
			var UTF8Text = _this.exportTextarea.val().replace(/\n/g, "\r\n").replace(/\r\r/g, "\r");
			var fileName = _this.chessInfo.title || "中国象棋";

            _this.localDownload(fileName + ".txt", UTF8Text, { type: "text/plain" });
		}
		else {
			_this.exportArea.trigger("submit");
		}
	});

	return this;
};

// 取得当前导出格式
vschess.load.prototype.getExportFormat = function(){
	return this._.exportFormat || "DhtmlXQ";
};

// 设置当前导出格式
vschess.load.prototype.setExportFormat = function(format, force){
	format = format || this.getExportFormat();
	this._.exportFormat = vschess.exportFormatList[format] ? format : this.getExportFormat();
	this.exportTextarea.removeClass().addClass("vschess-tab-body-export-textarea vschess-tab-body-export-textarea-format-" + format);
	this.exportFilename.val(this.chessInfo.title || "中国象棋");

	if (format === "TextBoard") {
		this.exportGenerate.removeClass("vschess-tab-body-export-current");
		this.exportCopy    .   addClass("vschess-tab-body-export-current");
		this.exportDownload.   addClass("vschess-tab-body-export-current");
		this.exportTextarea.val(vschess.textBoard(this.getCurrentFen(), this.options));
	}
    else if (format === "ChessDB") {
        this.exportGenerate.removeClass("vschess-tab-body-export-current");
        this.exportCopy    .   addClass("vschess-tab-body-export-current");
        this.exportDownload.   addClass("vschess-tab-body-export-current");

        var list = this.getMoveList();
        var fen = list.shift().split(" ").slice(0, 2).join(" ");
        var longData = list.length ? fen + " moves " + list.join(" ") : fen;

        this.exportTextarea.val(longData);
    }
	else if ((format === "DhtmlXQ") && !force && this.getNodeLength() >= vschess.bigBookCritical) {
		// 大棋谱需要加参数才同步
		this.exportCopy    .removeClass("vschess-tab-body-export-current");
		this.exportDownload.removeClass("vschess-tab-body-export-current");
		this.exportGenerate.   addClass("vschess-tab-body-export-current");
		this.exportTextarea.val("请点击“生成”按钮生成棋谱。");
    }
	else {
		this.exportGenerate.removeClass("vschess-tab-body-export-current");
		this.exportCopy    .   addClass("vschess-tab-body-export-current");
		this.exportDownload.   addClass("vschess-tab-body-export-current");
		this.exportTextarea.val(this.exportData[this.getExportFormat() + (this.getTurnForMove() ? "M" : "")]);
	}

	return this;
};

// 重建所有棋谱
vschess.load.prototype.rebuildExportAll = function(all){
	this.rebuildExportText();

	return this;
};


// 重建文本 TXT 格式棋谱
vschess.load.prototype.rebuildExportText = function(){
	var moveList  = this.moveNameList.Chinese .slice(0);
	var moveListM = this.moveNameList.ChineseM.slice(0);
	var startFen  = moveList .shift();
	var startFenM = moveListM.shift();
	this.exportData.Text  = vschess.moveListToText(moveList , startFen , this.commentList, this.chessInfo, this.getResultByCurrent());
	this.exportData.TextM = vschess.moveListToText(moveListM, startFenM, this.commentList, this.chessInfo, this.getResultByCurrent());
	return this;
};

// 重建东萍 DhtmlXQ 格式棋谱
vschess.load.prototype.rebuildExportDhtmlXQ = function(){
	this.exportData.DhtmlXQ  = vschess.nodeToData_DhtmlXQ(this.node, this.chessInfo);
	this.exportData.DhtmlXQM = vschess.turn_DhtmlXQ(this.exportData.DhtmlXQ);
	return this;
};


// 创建帮助区域
vschess.load.prototype.createHelp = function(){
	if (this._.helpAreaCreated) {
		return this;
	}

	this._.helpAreaCreated = true;
	var _this = this;
	var helpDetail = this.options.help.replace(/#quickStepOffsetRound#/g, this._.quickStepOffset / 2).replace(/#quickStepOffset#/g, this._.quickStepOffset);
	this.helpArea = $('<div class="vschess-help-area"></div>');
	this.helpArea.html('<div class="vschess-help-area-detail">' + helpDetail + '</div>');
	this.DOM.append(this.helpArea);
	this.helpAreaClose = $('<button type="button" class="vschess-button vschess-help-close">关 闭</button>');
	this.helpAreaClose.bind(this.options.click, function(){ _this.hideHelpArea(); });
	this.helpArea.append(this.helpAreaClose);
	return this;
};

// 刷新帮助信息
vschess.load.prototype.refreshHelp = function(){
	if (!this._.helpAreaCreated) {
		return this;
	}

	var helpDetail = this.options.help.replace(/#quickStepOffsetRound#/g, this._.quickStepOffset / 2).replace(/#quickStepOffset#/g, this._.quickStepOffset);
	this.helpArea.children(".vschess-help-area-detail").html(helpDetail);
	return this;
};

// 显示帮助区域
vschess.load.prototype.showHelpArea = function(){
	this.createHelp();
	this.helpArea.addClass("vschess-help-show");
	return this;
};

// 隐藏帮助区域
vschess.load.prototype.hideHelpArea = function(){
	if (!this._.helpAreaCreated) {
		return this;
	}

	this.helpArea.removeClass("vschess-help-show");
	return this;
};

// 创建棋局信息区域
vschess.load.prototype.createInfo = function(){
	var _this = this;
  this.infoTitle = $('<div class="vschess-tab-title vschess-tab-title-info">' + this.options.tagName.info + '</div>');
	this.infoArea  = $('<div class="vschess-tab-body vschess-tab-body-info"></div>');
	this.tabArea.children(".vschess-tab-title-info, .vschess-tab-body-info").remove();
	this.tabArea.append(this.infoTitle);
	this.tabArea.append(this.infoArea );
	this.infoTitle.bind(this.options.click, function(){ _this.showTab("info"); });
	this.createInfoList();
	return this;
};

// 创建棋局信息列表
vschess.load.prototype.createInfoList = function(){
	var _this = this;
	this.chessInfo = vschess.dataToInfo(this.chessData, this.options.parseType);
	this.setChessTitle(this.chessInfo && this.chessInfo.title || "中国象棋");
	this.infoList = $('<ul class="vschess-tab-body-info-list"></ul>');
	this.infoArea.append(this.infoList);
	this.insertInfoByCurrent();
	this.infoEdit  = $('<button type="button" class="vschess-button vschess-tab-body-info-edit" >编 辑</button>');
	this.infoEmpty = $('<button type="button" class="vschess-button vschess-tab-body-info-empty">清 空</button>');
	this.infoArea.append(this.infoEdit );
	this.infoArea.append(this.infoEmpty);
	this.infoEdit.bind(this.options.click, function(){ _this.showInfoEditor(); });

	this.infoEmpty.bind(this.options.click, function(){
		if (!confirm("确定要清空所有信息吗？")) {
			return false;
		}

		_this.chessInfo = {};
		_this.insertInfoByCurrent();
		_this.refreshInfoEditor();
		_this.rebuildExportAll();
		_this.setExportFormat();
	});

	return this;
};

// 填充当前棋谱信息
vschess.load.prototype.insertInfoByCurrent = function(){
	this.infoItem = {};
	this.infoList.empty();

	for (var i in this.chessInfo) {
		this.infoItem[i] = $('<li class="vschess-tab-body-info-item">' + vschess.info.name[i] + '：' + vschess.showText(this.chessInfo[i], i) + '</li>');
		this.infoList.append(this.infoItem[i]);
	}

	return this;
};

// 创建棋局信息编辑器
vschess.load.prototype.createInfoEditor = function(){
	if (this._.infoEditorCreated) {
		return this;
	}

	var _this = this;
	this._.infoEditorCreated = true;
	this.infoEditorArea = $('<div class="vschess-info-editor-area"></div>');
	this.infoEditorList = $('<ul class="vschess-info-editor-list"></ul>');
	this.infoEditorArea.append(this.infoEditorList);
	this.infoEditorItem = {};
	this.infoEditorItemName  = {};
	this.infoEditorItemValue = {};
	this.infoEditorItemAuto  = {};
	this.DOM.append(this.infoEditorArea);

	for (var i in vschess.info.name) {
		this.infoEditorItem     [i] = $('<li class="vschess-info-editor-item vschess-info-editor-item-' + i + '"></li>');
		this.infoEditorItemName [i] = $('<div class="vschess-info-editor-item-name vschess-info-editor-item-name-' + i + '">' + vschess.info.name[i] + '：</div></li>');
		this.infoEditorItemValue[i] = $('<input type="' + (i === "date" ? "date" : "text") + '" class="vschess-info-editor-item-value vschess-info-editor-item-value-' + i + '" />');
		this.infoEditorItem     [i].append(this.infoEditorItemName [i]);
		this.infoEditorItem     [i].append(this.infoEditorItemValue[i]);
		this.infoEditorList        .append(this.infoEditorItem     [i]);

		if (i === "result") {
			var radio_name = "vschess-info-editor-item-value-result-radio-name-" + vschess.guid();
			var r_randomId = "vschess-info-editor-item-value-result-label-id-r-" + vschess.guid();
			var b_randomId = "vschess-info-editor-item-value-result-label-id-b-" + vschess.guid();
			var d_randomId = "vschess-info-editor-item-value-result-label-id-d-" + vschess.guid();
			var u_randomId = "vschess-info-editor-item-value-result-label-id-u-" + vschess.guid();

			this.infoEditorItemValueResult = {
				r_label: $('<label class="vschess-info-editor-item-value-result-label vschess-info-editor-item-value-result-label-r" for="' + r_randomId + '">红胜</label>'),
				b_label: $('<label class="vschess-info-editor-item-value-result-label vschess-info-editor-item-value-result-label-b" for="' + b_randomId + '">黑胜</label>'),
				d_label: $('<label class="vschess-info-editor-item-value-result-label vschess-info-editor-item-value-result-label-d" for="' + d_randomId + '">和棋</label>'),
				u_label: $('<label class="vschess-info-editor-item-value-result-label vschess-info-editor-item-value-result-label-u" for="' + u_randomId + '">未知</label>'),
				r_radio: $('<input type="radio" name="' + radio_name + '" class="vschess-info-editor-item-value-result-radio vschess-info-editor-item-value-result-radio-r" id="' + r_randomId + '" />'),
				b_radio: $('<input type="radio" name="' + radio_name + '" class="vschess-info-editor-item-value-result-radio vschess-info-editor-item-value-result-radio-b" id="' + b_randomId + '" />'),
				d_radio: $('<input type="radio" name="' + radio_name + '" class="vschess-info-editor-item-value-result-radio vschess-info-editor-item-value-result-radio-d" id="' + d_randomId + '" />'),
				u_radio: $('<input type="radio" name="' + radio_name + '" class="vschess-info-editor-item-value-result-radio vschess-info-editor-item-value-result-radio-u" id="' + u_randomId + '" />')
			};

			this.infoEditorItem.result.append(this.infoEditorItemValueResult.r_radio);
			this.infoEditorItem.result.append(this.infoEditorItemValueResult.r_label);
			this.infoEditorItem.result.append(this.infoEditorItemValueResult.b_radio);
			this.infoEditorItem.result.append(this.infoEditorItemValueResult.b_label);
			this.infoEditorItem.result.append(this.infoEditorItemValueResult.d_radio);
			this.infoEditorItem.result.append(this.infoEditorItemValueResult.d_label);
			this.infoEditorItem.result.append(this.infoEditorItemValueResult.u_radio);
			this.infoEditorItem.result.append(this.infoEditorItemValueResult.u_label);
		}

		if (~vschess.autoInfo.indexOf(i)) {
			this.infoEditorItemAuto[i] = $('<button type="button" class="vschess-button vschess-info-editor-item-auto vschess-info-editor-item-auto-' + i + '" alt="根据当前分支自动识别' + vschess.info.name[i] + '" title="根据当前分支自动识别' + vschess.info.name[i] + '">识 别</button>');
			this.infoEditorItem    [i].append(this.infoEditorItemAuto[i]);
		}
	}

	this.setInfoEditorItemValueResult(this.infoEditorItemValue.result.val());
	this.infoEditorOK     = $('<button type="button" class="vschess-button vschess-info-editor-ok"    >确 定</button>');
	this.infoEditorEmpty  = $('<button type="button" class="vschess-button vschess-info-editor-empty" >清 空</button>');
	this.infoEditorCancel = $('<button type="button" class="vschess-button vschess-info-editor-cancel">取 消</button>');

	this.infoEditorOK.bind(this.options.click, function(){
		_this.chessInfo = _this.getInfoFromEditor();
		_this.setChessTitle(_this.chessInfo && _this.chessInfo.title || "中国象棋");
		_this.insertInfoByCurrent();
		_this.hideInfoEditor();
		_this.rebuildExportAll();
		_this.setExportFormat();
	});

	this.infoEditorEmpty.bind(this.options.click, function(){
		if (!confirm("确定要清空所有信息吗？")) {
			return false;
		}

		for (var i in vschess.info.name) {
			_this.infoEditorItemValue[i].val("");
		}
	});

	this.infoEditorCancel.bind(this.options.click, function(){ _this.hideInfoEditor(); });
	this.infoEditorArea.append(this.infoEditorOK    );
	this.infoEditorArea.append(this.infoEditorEmpty );
	this.infoEditorArea.append(this.infoEditorCancel);
	this.infoEditorItemValueResult.r_radio.bind(this.options.click, function(){ _this.infoEditorItemValue.result   .val("1-0"    ); });
	this.infoEditorItemValueResult.b_radio.bind(this.options.click, function(){ _this.infoEditorItemValue.result   .val("0-1"    ); });
	this.infoEditorItemValueResult.d_radio.bind(this.options.click, function(){ _this.infoEditorItemValue.result   .val("1/2-1/2"); });
	this.infoEditorItemValueResult.u_radio.bind(this.options.click, function(){ _this.infoEditorItemValue.result   .val("*"      ); });

	return this.refreshInfoEditor();
};

// 刷新棋局信息编辑器
vschess.load.prototype.refreshInfoEditor = function(){
	this.createInfoEditor();

	for (var i in vschess.info.name) {
		if (i === "result") {
			var result = vschess.dataText(this.chessInfo[i] || "", i);
			this.infoEditorItemValue.result.val(result);
			this.setInfoEditorItemValueResult(result);
		}
		else if (i === "date") {
			this.infoEditorItemValue[i].val(vschess.dateFormat(this.chessInfo[i] || "", i));
		}
		else {
			this.infoEditorItemValue[i].val(vschess.dataText(this.chessInfo[i] || "", i));
		}
	}

	return this.setChessTitle(this.chessInfo && this.chessInfo.title || "中国象棋");
};

// 根据结果设置选择结果单选按钮
vschess.load.prototype.setInfoEditorItemValueResult = function(result){
	this.createInfoEditor();

	switch (result) {
		case     "1-0": this.infoEditorItemValueResult.r_radio.attr("checked", "checked"); break;
		case     "0-1": this.infoEditorItemValueResult.b_radio.attr("checked", "checked"); break;
		case "1/2-1/2": this.infoEditorItemValueResult.d_radio.attr("checked", "checked"); break;
		default       : this.infoEditorItemValueResult.u_radio.attr("checked", "checked"); break;
	}

	return this;
};

// 设置棋盘标题
vschess.load.prototype.setChessTitle = function(title){
	this.title.text(title);
	return this;
};

// 显示棋局信息编辑器
vschess.load.prototype.showInfoEditor = function(){
	this.createInfoEditor();
	this.infoEditorArea.addClass("vschess-info-editor-show");
	return this;
};

// 隐藏棋局信息编辑器
vschess.load.prototype.hideInfoEditor = function(){
	if (!this._.infoEditorCreated) {
		return this;
	}

	this.infoEditorArea.removeClass("vschess-info-editor-show");
	return this;
};

// 从编辑器中获取最新棋谱信息数据
vschess.load.prototype.getInfoFromEditor = function(){
	var newInfo = {};

	for (var i in vschess.info.name) {
		var value = this.infoEditorItemValue[i].val();
		value && (newInfo[i] = value);
	}

	return newInfo;
};

// 获取当前对弈结果
vschess.load.prototype.getResultByCurrent = function(){
	if (this._.editCreated) {
		return this.infoEditorItemValue.result.val() || this.getAutoResultByCurrent();
	}

	return this.getAutoResultByCurrent();
};

// 自动识别当前分支的对弈结果
vschess.load.prototype.getAutoResultByCurrent = function(){
	var legalLength = this.legalList ? this.legalList.length : 0;
	var repeatLongThreatLength = this.repeatLongThreatMoveList ? this.repeatLongThreatMoveList.length : 0;
	var lastSituation = this.situationList[this.lastSituationIndex()];

	if (this.getBanRepeatLongThreat() && legalLength <= repeatLongThreatLength) {
		return lastSituation[0] === 1 ? "0-1" : "1-0";
	}

	return !vschess.hasLegalMove(lastSituation) ? lastSituation[0] === 1 ? "0-1" : "1-0" : "*";
};

// 创建本地保存链接标签
vschess.load.prototype.createLocalDownloadLink = function(){
	this.localDownloadLink = $('<a class="vschess-local-download-link"></a>').appendTo(this.DOM);
	return this;
};

// 本地保存
vschess.load.prototype.localDownload = function(filename, filedata, param){
	if (!vschess.localDownload) {
		return this;
	}

	param = $.extend({ type: "text/plain" }, param);
	var blob = new Blob([filedata], param);
	this.localDownloadLink.attr({ download: filename, href: URL.createObjectURL(blob) }).trigger("click");
	return this;
};

// 创建移动端额外标签按钮
vschess.load.prototype.createMobileTag = function () {
    var _this = this;

    this.mobileCloseTab = $('<div class="vschess-mobile-close-tab">棋<br />盘</div>');
    this.DOM.children(".vschess-mobile-close-tab").remove();
    this.DOM.append(this.mobileCloseTab);

    this.mobileCloseTab.bind(this.options.click, function(){
        _this.showTab("board");
    });

    this.mobileShowMoveList = $('<div class="vschess-mobile-show-move-list">着<br />法</div>');
    this.DOM.children(".vschess-mobile-show-move-list").remove();
    this.DOM.append(this.mobileShowMoveList);

    this.mobileShowMoveList.bind(this.options.click, function(){
        _this.showTab("move");
    });

    return this;
};

// 着法选择列表
vschess.load.prototype.createMoveSelectList = function(){
	this.DOM.children(".vschess-move-select-list").remove();
	this.moveSelectList = $('<ul class="vschess-move-select-list"></ul>');
	this.DOM.append(this.moveSelectList);
	return this;
};

// 刷新着法选择列表内所有着法
vschess.load.prototype.refreshMoveSelectListNode = function(){
	var _this = this;
	var startRound = this.situationList[0][1];
	var selectListNode = ['<li class="vschess-move-select-node-begin">===== 棋局开始' + (this.commentList[0] ? "*" : "") + ' =====</li>'];

	switch (this.getMoveFormat()) {
		default    : var moveList = this.getTurnForMove() ? this.moveNameList.ChineseM.slice(0) : this.moveNameList.Chinese.slice(0); break;
	}

	this.situationList[0][0] === 1 ? moveList.shift() : moveList[0] = "";

	if (this.situationList[0][0] === 1 || this.situationList[0][0] === 2 && moveList.length > 1) {
		for (var i = 0; i < moveList.length; ++i) {
			i % 2 || selectListNode.push('<li class="vschess-move-select-node-round">', startRound++, '.</li>');
			selectListNode.push('<li class="vschess-move-select-node-', moveList[i] ? "move" : "blank", '">');
			selectListNode.push(moveList[i], this.commentList[!!moveList[0] + i] && moveList[i] ? "*" : "", '</li>');
		}
	}

	this.moveSelectList.html(selectListNode.join(""));
	this.moveSelectListSteps = this.moveSelectList.children().not(".vschess-move-select-node-round, .vschess-move-select-node-blank");

	this.moveSelectListSteps.each(function(index){
		var each = $(this);
		index && _this.changeLengthList[index - 1] > 1 && each.addClass("vschess-move-select-node-change");
		each.bind(_this.options.click, function(){ _this.setBoardByStep(index); });
	});

	return this.refreshMoveSelectListNodeColor();
};

// 着法列表着色
vschess.load.prototype.refreshMoveSelectListNodeColor = function(){
	this.moveSelectListSteps || this.refreshMoveListNode();
	this.moveSelectListSteps.removeClass("vschess-move-select-node-lose vschess-move-select-node-threat vschess-move-select-node-normal");

	var legalLength = this.legalList ? this.legalList.length : 0;
	var repeatLongThreatLength = this.repeatLongThreatMoveList ? this.repeatLongThreatMoveList.length : 0;

	if (legalLength === 0) {
		this.moveSelectListSteps.eq(this.getCurrentStep()).addClass("vschess-move-select-node-lose");
	}
	else if (vschess.checkThreat(this.situationList[this.getCurrentStep()])) {
		this.moveSelectListSteps.eq(this.getCurrentStep()).addClass("vschess-move-select-node-threat");
	}
	else if (this.getBanRepeatLongThreat() && legalLength <= repeatLongThreatLength) {
			this.moveSelectListSteps.eq(this.getCurrentStep()).addClass("vschess-move-select-node-lose");
	}
	else {
		this.moveSelectListSteps.eq(this.getCurrentStep()).addClass("vschess-move-select-node-normal");
	}

	this.setMoveLeaveHide();
	return this;
};

// 避免当前着法进入滚动区域外
vschess.load.prototype.setMoveLeaveHide = function(){
	var bottomLine           = this.moveSelectList.height() - this.moveSelectListSteps.first().height();
	var currentTop           = this.moveSelectListSteps.eq(this.getCurrentStep()).position().top;
	var currentScrollTop     = this.moveSelectList.scrollTop();
	currentTop > bottomLine	&& this.moveSelectList.scrollTop(currentScrollTop + currentTop - bottomLine	);
	currentTop < 0			&& this.moveSelectList.scrollTop(currentScrollTop + currentTop				);
	return this;
};

// 变招选择列表
vschess.load.prototype.createChangeSelectList = function(){
	this.DOM.children(".vschess-change-select-title, .vschess-change-select-list").remove();
	this.changeSelectTitle = $('<div class="vschess-change-select-title"></div>');
	this.changeSelectList  = $('<ul class="vschess-change-select-list"></ul>');
	this.DOM.append(this.changeSelectTitle);
	this.DOM.append(this.changeSelectList);
	return this;
};

// 刷新变招选择列表内所有着法
vschess.load.prototype.refreshChangeSelectListNode = function(){
	if (this.getCurrentStep() <= 0) {
		this.changeSelectTitle.text("提示信息");
		this.changeSelectList.empty();

		for (var i = 0; i < this.options.startTips.length; ++i) {
			this.changeSelectList.append('<li class="vschess-change-select-tips">' + this.options.startTips[i] + '</li>');
		}

		return this;
	}

	var _this = this;
	var selectListNode = [];
	var parentNode = this.selectDefault(this.getCurrentStep() - 1);
	var changeList  = parentNode.next;
	var currentNodeIndex = this.currentNodeList[this.getCurrentStep()];

	switch (this.getMoveFormat()) {
		default    : var converter = vschess.Node2Chinese; break;
	}

	for (var i = 0; i < changeList.length; ++i) {
		var changeMove	= this.getTurnForMove() ? vschess.turnMove(changeList[i].move) : changeList[i].move;
		var prevFen		= this.getFenByStep(this.getCurrentStep() - 1);

		selectListNode.push('<li class="vschess-change-select-node">');
		selectListNode.push('<span class="vschess-change-select-node-text vschess-change-select-node-move">');
		selectListNode.push(converter(changeMove, prevFen, this.options).move, changeList[i].comment ? "*" : "", '</span>');
		selectListNode.push('<span class="vschess-change-select-node-text vschess-change-select-node-up">上移</span>');
		selectListNode.push('<span class="vschess-change-select-node-text vschess-change-select-node-down">下移</span>');
		selectListNode.push('<span class="vschess-change-select-node-text vschess-change-select-node-delete">删除</span>');
		selectListNode.push('</li>');
	}

	this.changeSelectTitle.text("变招列表");
	this.changeSelectList.html(selectListNode.join(""));
	this.changeSelectListChanges = this.changeSelectList.children();
	this.changeSelectListChanges.first().addClass("vschess-change-select-node-first");
	this.changeSelectListChanges.last ().addClass("vschess-change-select-node-last" );

	this.changeSelectListChanges.each(function(index){
		var each = $(this);
		var move = changeList[index].move;
		index === currentNodeIndex && each.addClass("vschess-change-select-node-current");
		each.hasClass("vschess-change-select-node-current") && each.hasClass("vschess-change-select-node-first") && each.addClass("vschess-change-select-node-current-and-first");
		each.hasClass("vschess-change-select-node-current") && each.hasClass("vschess-change-select-node-last" ) && each.addClass("vschess-change-select-node-current-and-last" );

		each.bind(_this.options.click, function(){
			_this.setMoveDefaultAtNode(move, _this.getCurrentStep() - 1 ) && _this.rebuildSituation().refreshBoard().refreshMoveSelectListNode();
		});

		each.children(".vschess-change-select-node-up").bind(_this.options.click, function(e){
			e.stopPropagation();

			if (index <= 0) {
				return false;
			}

			var prevTarget = changeList[index - 1];
			changeList[index - 1] = changeList[index];
			changeList[index    ] = prevTarget;

			if (parentNode.defaultIndex === index) {
				parentNode.defaultIndex = index - 1;
			}
			else if (parentNode.defaultIndex === index - 1) {
				parentNode.defaultIndex = index;
			}

			_this.rebuildSituation().refreshBoard().refreshMoveSelectListNode();
		});

		each.children(".vschess-change-select-node-down").bind(_this.options.click, function(e){
			e.stopPropagation();

			if (index >= changeList.length - 1) {
				return false;
			}

			var prevTarget = changeList[index + 1];
			changeList[index + 1] = changeList[index];
			changeList[index    ] = prevTarget;

			if (parentNode.defaultIndex === index) {
				parentNode.defaultIndex = index + 1;
			}
			else if (parentNode.defaultIndex === index + 1) {
				parentNode.defaultIndex = index;
			}

			_this.rebuildSituation().refreshBoard().refreshMoveSelectListNode();
		});

		each.children(".vschess-change-select-node-delete").bind(_this.options.click, function(e){
			e.stopPropagation();

			if (!confirm("确定要删除该着法吗？该着法及之后的所有着法都将被删除！")) {
				return false;
			}

			for (var i = index; i < changeList.length; ++i) {
				changeList[i] = changeList[i + 1];
			}

			if (parentNode.defaultIndex === index) {
				parentNode.defaultIndex = 0;
			}
			else if (parentNode.defaultIndex > index) {
				--parentNode.defaultIndex;
			}

			--changeList.length;
			_this.rebuildSituation().refreshBoard().refreshMoveSelectListNode().refreshNodeLength();
		});
	});

	this.setChangeLeaveHide();
	return this;
};

// 避免当前变招进入滚动区域外
vschess.load.prototype.setChangeLeaveHide = function(){
	var bottomLine           = this.changeSelectList.height() - this.changeSelectListChanges.first().height();
	var currentTop           = this.changeSelectListChanges.eq(this.currentNodeList[this.getCurrentStep()]).position().top;
	var currentScrollTop     = this.changeSelectList.scrollTop();
	currentTop > bottomLine	&& this.changeSelectList.scrollTop(currentScrollTop + currentTop - bottomLine);
	currentTop < 0			&& this.changeSelectList.scrollTop(currentScrollTop + currentTop			 );
	return this;
};

// 刷新着法列表及变招列表
vschess.load.prototype.refreshMoveListNode = function(){
	return this.refreshMoveSelectListNode().refreshChangeSelectListNode();
};

// 设置当前着法列表格式
vschess.load.prototype.setMoveFormat = function(format){
	switch (format) {
		default    : this._.moveFormat = "chinese"	; break;
	}

	return this;
};

// 取得当前着法列表格式
vschess.load.prototype.getMoveFormat = function(){
	return this._.moveFormat;
};

// 移动一枚棋子
vschess.load.prototype.movePieceByPieceIndex = function(from, to, animationTime, callback, callbackIllegal){
	// 动画过程中，直接跳过
	if (this.animating) {
		return this;
	}

	if (typeof animationTime === "function") {
		callbackIllegal = callback;
		callback = animationTime;
		animationTime = 0;
	}

	from = vschess.limit(from, 0, 89);
	to   = vschess.limit(to  , 0, 89);
	animationTime = vschess.limit(animationTime, 0, Infinity);

	var From = vschess.b2i[vschess.turn[this.getTurn()][from]];
	var To   = vschess.b2i[vschess.turn[this.getTurn()][to  ]];
	var Move = From + To;

	// 着法不合法，不移动棋子
	var isBanRepeatLongThreat = this.getBanRepeatLongThreat() && ~this.repeatLongThreatMoveList.indexOf(Move);
	var isBanRepeatLongKill   = this.getBanRepeatLongKill  () && ~this.repeatLongKillMoveList  .indexOf(Move);

	if (!~this.legalMoveList.indexOf(Move) || isBanRepeatLongThreat || isBanRepeatLongKill) {
		typeof callbackIllegal === "function" && callbackIllegal();
		return this;
	}

	// 动画过渡，即动画时间大于 100，100毫秒以下效果很差，直接屏蔽
	if (animationTime >= 100) {
		var _this = this;
		this.animating = true;
		this.clearSelect();
		this.clearSelect(-1);
		this.clearPiece(from);
		this.clearPiece(-1);
		this.setSelectByPieceIndex(from);
		this.setSelectByPieceIndex(-1);

		var ua = navigator.userAgent.toLowerCase();
		var isIE6 = ~ua.indexOf("msie 6");
		var isIE7 = ~ua.indexOf("msie 7");
		var isIE8 = ~ua.indexOf("msie 8");

		// 低版本 IE 模式下，使用 js 的动画效果
		if (isIE6 || isIE7 || isIE8) {
			var _playSound = true;
			var finishHandlerRunned = false;

			var finishHandler = function(){
				_this.setMoveDefaultAtNode(Move) && _this.rebuildSituation().refreshMoveSelectListNode();
				_this.setBoardByOffset(1);
				_this.setSelectByStep();
				_this.animatePiece.hide();
				_playSound && _this.playSoundBySituation();
				_this.animating = false;
				finishHandlerRunned = true;

				_this.pieceRotateDeg[to]   = _this.pieceRotateDeg[from];
				_this.pieceRotateDeg[from] = Math.random() * 360;
				_this.getPieceRotate() ? _this.loadPieceRotate() : _this.clearPieceRotate();

				typeof _this.callback_afterAnimate === "function" && _this.callback_afterAnimate();
				typeof callback === "function" && callback();
			};

			var sIndex = vschess.b2s[vschess.turn[this.getTurn()][from]];
			var piece  = this.situationList[this.getCurrentStep()][sIndex];

			this.getPieceRotate() ? this.animatePiece.children("span").attr({ style: vschess.degToRotateCSS(this.pieceRotateDeg[from]) }) : this.animatePiece.children("span").removeAttr("style");

			this.animatePiece.addClass("vschess-piece-" + vschess.n2f[piece]).css({
				top : this.piece.eq(from).position().top,
				left: this.piece.eq(from).position().left
			}).show().animate({
				top : this.piece.eq(to).position().top,
				left: this.piece.eq(to).position().left
			}, animationTime, finishHandler);

			this.stopAnimate = function(playSound){
				typeof playSound !== "undefined" && (_playSound = playSound);
				_this.animatePiece.stop();
			};

			setTimeout(function(){ finishHandlerRunned || finishHandler(); }, animationTime + 500);
		}

		// 其他浏览器使用原生 CSS3 动画效果
		else {
			var finishHandlerRunned = false;

			var finishHandler = function(playSound){
				var _playSound = true;
				typeof playSound !== "undefined" && (_playSound = playSound);

				_this.setMoveDefaultAtNode(Move) && _this.rebuildSituation().refreshMoveSelectListNode();
				_this.setBoardByOffset(1);
				_this.setSelectByStep();
				_this.animatePiece.hide().css({ "-webkit-transition": "0ms", "-moz-transition": "0ms", "-ms-transition": "0ms", "-o-transition": "0ms", "transition": "0ms" });
				_playSound && _this.playSoundBySituation();
				_this.animating = false;

				setTimeout(function(){
					_this.animatePiece.hide().css({
						"-webkit-transform": "translate3d(0px, 0px, 0px)",
						   "-moz-transform": "translate3d(0px, 0px, 0px)",
							"-ms-transform": "translate3d(0px, 0px, 0px)",
						     "-o-transform": "translate3d(0px, 0px, 0px)",
						        "transform": "translate3d(0px, 0px, 0px)"
					});
				}, vschess.threadTimeout);

				var Evt = _this.animatePiece[0];
				Evt.removeEventListener("webkitTransitionEnd", finishHandler);
				Evt.removeEventListener(   "mozTransitionEnd", finishHandler);
				Evt.removeEventListener(    "msTransitionEnd", finishHandler);
				Evt.removeEventListener(     "oTransitionEnd", finishHandler);
				Evt.removeEventListener(      "transitionend", finishHandler);

				finishHandlerRunned = true;

				_this.pieceRotateDeg[to]   = _this.pieceRotateDeg[from];
				_this.pieceRotateDeg[from] = Math.random() * 360;
				_this.getPieceRotate() ? _this.loadPieceRotate() : _this.clearPieceRotate();

				typeof _this.callback_afterAnimate === "function" && _this.callback_afterAnimate();
				typeof callback === "function" && callback();
			};

			var deltaX = this.piece.eq(to).position().left - this.piece.eq(from).position().left;
			var deltaY = this.piece.eq(to).position().top  - this.piece.eq(from).position().top;
			var sIndex = vschess.b2s[vschess.turn[this.getTurn()][from]];
			var piece  = this.situationList[this.getCurrentStep()][sIndex];

			this.getPieceRotate() ? this.animatePiece.children("span").attr({ style: vschess.degToRotateCSS(this.pieceRotateDeg[from]) }) : this.animatePiece.children("span").removeAttr("style");

			var Evt = this.animatePiece.addClass("vschess-piece-" + vschess.n2f[piece]).css({
				top : this.piece.eq(from).position().top,
				left: this.piece.eq(from).position().left,
				"-webkit-transition": animationTime + "ms",
				   "-moz-transition": animationTime + "ms",
					"-ms-transition": animationTime + "ms",
				     "-o-transition": animationTime + "ms",
				        "transition": animationTime + "ms"
			}).show()[0];

			Evt.addEventListener("webkitTransitionEnd", finishHandler);
			Evt.addEventListener(   "mozTransitionEnd", finishHandler);
			Evt.addEventListener(    "msTransitionEnd", finishHandler);
			Evt.addEventListener(     "oTransitionEnd", finishHandler);
			Evt.addEventListener(      "transitionend", finishHandler);

			setTimeout(function(){
				_this.animatePiece.css({
					"-webkit-transform": "translate3d(" + deltaX + "px, " + deltaY + "px, 0px)",
					   "-moz-transform": "translate3d(" + deltaX + "px, " + deltaY + "px, 0px)",
						"-ms-transform": "translate3d(" + deltaX + "px, " + deltaY + "px, 0px)",
					     "-o-transform": "translate3d(" + deltaX + "px, " + deltaY + "px, 0px)",
					        "transform": "translate3d(" + deltaX + "px, " + deltaY + "px, 0px)"
				});
			}, vschess.threadTimeout);

			this.stopAnimate = finishHandler;
			setTimeout(function(){ finishHandlerRunned || finishHandler(); }, animationTime + 500);
		}
	}

	// 无动画过渡，即动画时间为 0
	else {
		this.stopAnimate = function(){};
		this.setMoveDefaultAtNode(Move) && this.rebuildSituation().refreshMoveSelectListNode();
		this.setBoardByOffset(1);
		this.setSelectByStep();
		this.playSoundBySituation();
		typeof this.callback_afterAnimate === "function" && this.callback_afterAnimate();
		typeof callback === "function" && callback();
	}

	return this;
};

// 以动画方式过渡到下一个局面
vschess.load.prototype.animateToNext = function(animationTime, callback){
	if (this.animating || this.getCurrentStep() >= this.lastSituationIndex()) {
		return this;
	}

	var from = vschess.turn[this.getTurn()][vschess.i2b[this.getMoveByStep(this.getCurrentStep() + 1).substring(0, 2)]];
	var to   = vschess.turn[this.getTurn()][vschess.i2b[this.getMoveByStep(this.getCurrentStep() + 1).substring(2, 4)]];
	this.movePieceByPieceIndex(from, to, vschess.limit(animationTime, 0, Infinity), callback);
	return this;
};

// 设置动画时间
vschess.load.prototype.setAnimationTime = function(animationTime){
	this._.animationTime = vschess.limit(animationTime, 0, Infinity);
	return this;
};

// 取得动画时间
vschess.load.prototype.getAnimationTime = function(animationTime){
	return this._.animationTime >= this._.playGap * 100 ? this._.playGap * 50 : this._.animationTime;
};

// 设置禁止重复长打状态
vschess.load.prototype.setBanRepeatLongThreat = function(banRepeatLongThreat){
	this._.banRepeatLongThreat = !!banRepeatLongThreat;
	this.setConfigItemValue("banRepeatLongThreat", this._.banRepeatLongThreat);
	return this;
};

// 取得禁止重复长打状态
vschess.load.prototype.getBanRepeatLongThreat = function(){
	return this._.banRepeatLongThreat;
};

// 设置禁止重复一将一杀状态
vschess.load.prototype.setBanRepeatLongKill = function(banRepeatLongKill){
	this._.banRepeatLongKill = !!banRepeatLongKill;
	this.setConfigItemValue("banRepeatLongKill", this._.banRepeatLongKill);
	return this;
};

// 取得禁止重复一将一杀状态
vschess.load.prototype.getBanRepeatLongKill = function(){
	return this._.banRepeatLongKill;
};

// 设置违例提示状态
vschess.load.prototype.setIllegalTips = function(illegalTips){
	this._.illegalTips = !!illegalTips;
	this.setConfigItemValue("illegalTips", this._.illegalTips);
	return this;
};

// 取得违例提示状态
vschess.load.prototype.getIllegalTips = function(){
	return this._.illegalTips;
};

// 重建所有局面，一般用于变招切换和节点发生变化
vschess.load.prototype.rebuildSituation = function(){
	this.situationList = [vschess.fenToSituation(this.node.fen)];
	this.fenList   = [this.node.fen];
	this.moveList  = [this.node.fen];
	this.eatStatus = [false];
	this.commentList = [this.node.comment || ""];
	this.changeLengthList = [ ];
	this.currentNodeList  = [0];
	this.nodeList = [this.node];

	var turnFen = vschess.turnFen(this.node.fen);

	this.moveNameList = {
		Chinese	: [this.node.fen], ChineseM	: [turnFen]
	};

	for (var currentNode = this.node; currentNode.next.length; ) {
		this.changeLengthList.push(currentNode.next.length );
		this.currentNodeList .push(currentNode.defaultIndex);
		currentNode = currentNode.next[currentNode.defaultIndex];
		this.nodeList.push(currentNode);

		var from = vschess.i2s[currentNode.move.substring(0, 2)];
		var to   = vschess.i2s[currentNode.move.substring(2, 4)];
		var lastSituation = this.situationList[this.lastSituationIndex()].slice(0);
		var prevFen = vschess.situationToFen(lastSituation);
		var prevPieceCount = vschess.countPieceLength(lastSituation);

		lastSituation[to  ] = lastSituation[from];
		lastSituation[from] = 1;
		lastSituation[0]    = 3  -   lastSituation[0];
		lastSituation[0]  === 1 && ++lastSituation[1];

		this.eatStatus		.push(vschess.countPieceLength(lastSituation) !== prevPieceCount);
		this.moveList		.push(currentNode.move);
		this.commentList	.push(currentNode.comment || "");
		this.situationList	.push(lastSituation);
		this.fenList		.push(vschess.situationToFen(lastSituation));

		var wxf  = vschess.Node2WXF(currentNode.move, prevFen).move;
		var wxfM = wxf.charCodeAt(1) > 96 ? vschess.Node2WXF(vschess.turnMove(currentNode.move), vschess.turnFen(prevFen)).move : vschess.turnWXF(wxf);

		this.moveNameList.Chinese .push(vschess.Node2Chinese(wxf , prevFen, this.options));
		this.moveNameList.ChineseM.push(vschess.Node2Chinese(wxfM, prevFen, this.options));
	}

	return this.rebuildExportAll().setExportFormat();
};

// 选择指定默认节点
vschess.load.prototype.selectDefault = function(step){
	step = vschess.limit(step, 0, this.lastSituationIndex(), this.getCurrentStep());
	var currentNode = this.node;

	for (var i = 0; i < step; ++i) {
		currentNode = currentNode.next[currentNode.defaultIndex];
	}

	return currentNode;
};

// 节点内是否含有指定着法
vschess.load.prototype.hasMoveAtNode = function(move, step){
	var nextList = this.selectDefault(vschess.limit(step, 0, this.lastSituationIndex(), this.getCurrentStep())).next;

	for (var i = 0; i < nextList.length; ++i) {
		if (nextList[i].move === move) {
			return true;
		}
	}

	return false;
};

// 节点增加着法
vschess.load.prototype.addNodeByMoveName = function(move, step){
	step = vschess.limit(step, 0, this.lastSituationIndex(), this.getCurrentStep());

	if (!this.hasMoveAtNode(move, step)) {
		this.selectDefault(step).next.push({ move: move, comment: "", next: [], defaultIndex: 0 });
		++this._.nodeLength;
	}

	return this;
};

// 将节点内指定着法设为默认着法，并返回节点是否发生变化
vschess.load.prototype.setMoveDefaultAtNode = function(move, step){
	step = vschess.limit(step, 0, this.lastSituationIndex(), this.getCurrentStep());
	var currentNode = this.selectDefault(step);

	if (currentNode.next.length && currentNode.next[currentNode.defaultIndex].move === move) {
		return false;
	}

	for (var i = 0; i < currentNode.next.length; ++i) {
		if (currentNode.next[i].move === move) {
			currentNode.defaultIndex = i;
			this.setSaved(false);
			return true;
		}
	}

	this.addNodeByMoveName(move, step);
	currentNode.defaultIndex = currentNode.next.length - 1;
	this.setSaved(false);
	return true;
};

// 取得着法列表
vschess.load.prototype.getMoveNameList = function(format, isMirror){
	typeof isMirror === "undefined" && (isMirror = this.getTurnForMove());

	switch (format) {
		default    : return isMirror ? this.moveNameList.ChineseM.slice(0) : this.moveNameList.Chinese.slice(0);
	}

	return this;
};

// 刷新节点数
vschess.load.prototype.refreshNodeLength = function(){
	var total = 1;

	function countNode(node){
		total += node.next.length;

		for (var i = 0; i < node.next.length; ++i) {
			countNode(node.next[i]);
		}
	}

	countNode(this.node);
	this._.nodeLength = total;
	return this;
};

// 取得节点数
vschess.load.prototype.getNodeLength = function(){
	return this._.nodeLength;
};

// 设置当前节点树
vschess.load.prototype.setNode = function(node){
	this.node = node;
	this.refreshNodeLength();
	return this;
};

// 棋子单击事件绑定
vschess.load.prototype.pieceClick = function(){
	var _this = this;

	this.piece.each(function(index){
		$(this).bind(_this.options.click, function(){
			// 是本方棋子，切换选中状态
			if (_this.isPlayer(index)) {
				if (_this.getClickResponse() > 1 && _this.isR(index) || (_this.getClickResponse() & 1) && _this.isB(index)) {
					_this.toggleSelectByPieceIndex(index);
					_this.playSound("click");
				}
			}

			// 不是本方棋子，即为走子目标或空白点
			else {
				// 违例提示
				if (_this.getIllegalTips()) {
					var From = vschess.b2i[vschess.turn[_this.getTurn()][_this.getCurrentSelect()]];
					var To   = vschess.b2i[vschess.turn[_this.getTurn()][index]];
					var Move = From + To;

					if (_this.getBanRepeatLongThreat() && ~_this.repeatLongThreatMoveList.indexOf(Move)) {
						alert("禁止重复长打！");
					}

					if (_this.getBanRepeatLongKill() && ~_this.repeatLongKillMoveList.indexOf(Move)) {
						alert("禁止重复一将一杀！");
					}
				}

				// 合法着法，移动棋子
				if (_this.getLegalByPieceIndex(_this.getCurrentSelect(), index)) {
					_this.callback_beforeClickAnimate();
					_this.movePieceByPieceIndex(_this.getCurrentSelect(), index, _this.getAnimationTime(), function(){ _this.callback_afterClickAnimate(); });
				}

				// 不合法着法，播放非法着法音效
				else if (~_this.getCurrentSelect()) {
					_this.playSound("illegal");
				}
			}
		});
	});

	return this;
};

// 设置单击响应状态
vschess.load.prototype.setClickResponse = function(clickResponse){
	this._.clickResponse = vschess.limit(clickResponse, 0, 3);
	return this;
};

// 取得单击相应状态
vschess.load.prototype.getClickResponse = function(){
	return this._.clickResponse;
};

// 设置走子提示状态
vschess.load.prototype.setMoveTips = function(moveTips){
	this._.moveTips = !!moveTips;
	this.setConfigItemValue("moveTips", this._.moveTips);
	return this;
};

// 取得走子提示状态
vschess.load.prototype.getMoveTips = function(){
	return this._.moveTips;
};

// 设置指定棋子合法目标格状态，-1 表示动画棋子
vschess.load.prototype.setLegalByPieceIndex = function(index){
	index = vschess.limit(index, -1, 89);
	~index ? this.piece.eq(index).addClass("vschess-piece-S") : this.animatePiece.addClass("vschess-piece-S");
	return this;
};

// 获取指定棋子合法目标格状态
vschess.load.prototype.getLegalByPieceIndex = function(startIndex, targetIndex){
	 startIndex		= vschess.limit( startIndex, 0, 89, this.getCurrentSelect());
	targetIndex		= vschess.limit(targetIndex, 0, 89, this.getCurrentSelect());
	var  startPos	= vschess.b2i[vschess.turn[this.getTurn()][vschess.limit( startIndex, 0, 89)]];
	var targetPos	= vschess.b2i[vschess.turn[this.getTurn()][vschess.limit(targetIndex, 0, 89)]];
	var move		= startPos + targetPos;

	if (this.getBanRepeatLongThreat() && ~this.repeatLongThreatMoveList.indexOf(move)) {
		return false;
	}

	if (this.getBanRepeatLongKill() && ~this.repeatLongKillMoveList.indexOf(move)) {
		return false;
	}

	return !!~this.legalMoveList.indexOf(startPos + targetPos);
};

// 设置指定棋子选中状态，-1 表示动画棋子
vschess.load.prototype.setSelectByPieceIndex = function(index){
	index = vschess.limit(index, -1, 89);
	~index ? this.setCurrentSelect(index).piece.eq(index).addClass("vschess-piece-s") : this.animatePiece.addClass("vschess-piece-s");
	return this;
};

// 获取指定棋子选中状态
vschess.load.prototype.getSelectByPieceIndex = function(index){
	return this.piece.eq(vschess.limit(index, 0, 89)).hasClass("vschess-piece-s");
};

// 设置合法目标格提示状态
vschess.load.prototype.setLegalTargetByStartIndex = function(index){
	index = vschess.limit(index, 0, 89);
	var _this = this;
	this.piece.each(function(pieceIndex){ _this.getLegalByPieceIndex(index, pieceIndex) && _this.setLegalByPieceIndex(pieceIndex); });
	return this;
};

// 切换棋子选中状态
vschess.load.prototype.toggleSelectByPieceIndex = function(index){
	index = vschess.limit(index, 0, 89);

	if (this.piece.eq(index).hasClass("vschess-piece-s")) {
		this.clearSelect();
		this.callback_unSelectPiece();
	}
	else {
		this.clearSelect();
		this.setSelectByPieceIndex(index);
		this.getMoveTips() && this.setLegalTargetByStartIndex(index);
		this.callback_selectPiece();
	}

	return this;
};

// 根据局面为起始点及目标点棋子添加方框
vschess.load.prototype.setSelectByStep = function(step){
	step = vschess.limit(step, 0, this.lastSituationIndex(), this.getCurrentStep());

	if (step <= 0) {
		return this;
	}

	var from = vschess.i2s[this.getMoveByStep(step).substring(0, 2)];
	var to   = vschess.i2s[this.getMoveByStep(step).substring(2, 4)];
	var currentSelect = this.getCurrentSelect();
	this.setSelectByPieceIndex(vschess.turn[this.getTurn()][vschess.s2b[from]]);
	this.setSelectByPieceIndex(vschess.turn[this.getTurn()][vschess.s2b[to  ]]);
	this.setCurrentSelect(currentSelect);
	return this;
};

// 设置当前选中的棋子编号，-1 表示没有被选中的棋子
vschess.load.prototype.setCurrentSelect = function(currentSelect){
	this._.currentSelect = vschess.limit(currentSelect, -1, 89, -1);
	return this;
};

// 取得当前选中的棋子编号，-1 表示没有被选中的棋子
vschess.load.prototype.getCurrentSelect = function(){
	return this._.currentSelect;
};


// 显示指定索引号的局面，负值表示从最后一个局面向前
vschess.load.prototype.setBoardByStep = function(step, indexUnChange){
	step = vschess.limit(step, 0, this.lastSituationIndex(), this.getCurrentStep());
	var _this = this;
	this._.currentStep = vschess.limit(step, 0, this.lastSituationIndex());
	this.clearBoard(  );
	this.clearBoard(-1);
	this.animating = false;

	this.piece.each(function(index){
		var piece = _this.situationList[_this.getCurrentStep()][vschess.b2s[vschess.turn[_this.getTurn()][index]]];
		piece > 1 && $(this).addClass("vschess-piece-" + vschess.n2f[piece]);
	});

	this.getPieceRotate() ? this.loadPieceRotate() : this.clearPieceRotate();

	// 从 setTurn 方法过来的无需更新合法列表，提高执行速度
	if (!indexUnChange) {
		this.legalList     = vschess.legalList    (this.situationList[this.getCurrentStep()]);
		this.legalMoveList = vschess.legalMoveList(this.situationList[this.getCurrentStep()]);
		this.repeatLongThreatMoveList = this.getBanRepeatLongThreat() ? this.getRepeatLongThreatMove() : [];
		this.repeatLongKillMoveList   = this.getBanRepeatLongKill  () ? this.getRepeatLongKillMove  () : [];
	}

	this.setSelectByStep();
	this.refreshMoveSelectListNodeColor();
	this.refreshChangeSelectListNode();
	this.setCommentByStep();
    this.getExportFormat() === "TextBoard" && this.setExportFormat("TextBoard");
    this.getExportFormat() === "ChessDB"   && this.setExportFormat("ChessDB"  );
	return this;
};

// 显示指定步数后的局面，正数向后，负数向前，默认为下一步
vschess.load.prototype.setBoardByOffset = function(offset){
	return this.setBoardByStep(vschess.limit(this.getCurrentStep() + vschess.limit(offset, -Infinity, Infinity, 1), 0, this.lastSituationIndex()));
};

// 刷新棋盘，一般用于设置棋盘方向之后
vschess.load.prototype.refreshBoard = function(indexUnChange){
	return this.setBoardByStep(this.getCurrentStep(), indexUnChange).refreshMoveListNode();
};

// 设置棋盘方向，0(0x00) 不翻转，1(0x01) 左右翻转，2(0x10) 上下翻转，3(0x11) 上下翻转 + 左右翻转
vschess.load.prototype.setTurn = function(turn){
	this._.turn = vschess.limit(turn, 0, 3, 0);
	arguments[1] || this.setConfigItemValue("turnX", !!(turn & 1));
	arguments[1] || this.setConfigItemValue("turnY",    turn > 1 );
	return this.refreshBoard(true).setExportFormat().refreshColumnIndex();
};

// 取得棋盘方向
vschess.load.prototype.getTurn = function(){
	return this._.turn;
};

// 取得棋盘着法翻转状态
vschess.load.prototype.getTurnForMove = function(){
	return this.getTurn() >> 1 !== (this.getTurn() & 1);
};

// 取得当前局面号
vschess.load.prototype.getCurrentStep = function(){
	return this._.currentStep;
};

// 取得当前走棋方，1 为红方，2 为黑方
vschess.load.prototype.getCurrentPlayer = function(){
	return this.situationList[this.getCurrentStep()][0];
};

// 刷新列号
vschess.load.prototype.refreshColumnIndex = function(turn){
	this.columnIndexR.removeClass("vschess-column-index-a vschess-column-index-b");
	this.columnIndexB.removeClass("vschess-column-index-a vschess-column-index-b");

	if (vschess.limit(turn, 0, 3, this.getTurn()) > 1) {
		this.columnIndexR.addClass("vschess-column-index-a");
		this.columnIndexB.addClass("vschess-column-index-b");
	}
	else {
		this.columnIndexR.addClass("vschess-column-index-b");
		this.columnIndexB.addClass("vschess-column-index-a");
	}

	return this;
};

// 设置棋子随机旋转状态
vschess.load.prototype.setPieceRotate = function(status){
	this._.pieceRotate = !!status;
	return this.setConfigItemValue("pieceRotate", this._.pieceRotate);
};

// 取得棋子随机旋转状态
vschess.load.prototype.getPieceRotate = function(){
	return this._.pieceRotate;
};

// 初始化棋子旋转角度
vschess.load.prototype.initPieceRotateDeg = function(){
	this.pieceRotateDeg = [];

	for (var i = 0; i < 90; ++i) {
		this.pieceRotateDeg.push(Math.random() * 360);
	}

	return this;
};

// 设置棋子旋转
vschess.load.prototype.loadPieceRotate = function(){
	var _this = this;

	this.piece.children("span").each(function(k){
		$(this).attr({ style: vschess.degToRotateCSS(_this.pieceRotateDeg[k]) });
	});

	return this;
};

// 移除棋子旋转
vschess.load.prototype.clearPieceRotate = function(){
	this.piece.children("span").removeAttr("style");
	return this;
};

// 音效播放组件
vschess.load.prototype.playSound = function(name){
	this.getSound() && vschess.soundObject[this.options.soundStyle + "-" + name](this.getVolume());
	return this;
};

// 根据局面播放音效
vschess.load.prototype.playSoundBySituation = function(step){
	step = vschess.limit(step, 0, this.lastSituationIndex(), this.getCurrentStep());

	if (step <= 0) {
		return this;
	}

	// 着法朗读
	if (this.getSpeakMove()) {
		var move = this.getMoveNameList()[this.getCurrentStep()];
		// TTS 部分读音有错误，用同音字强行纠正
		move = move.replace(/\u5352/g, "足");
		move = move.replace(/\u76f8/g, "象");
		move = move.replace(/\u5c06/g, "酱");
		move = move.replace(/\u4e00/g, "医");
		move = move.replace(/\uff11/g, "医");
		this.speakMove(move);
	}
	// 普通音效
	else {
		var fromPiece = this.situationList[step - 1][vschess.i2s[this.getMoveByStep(step).substring(0, 2)]];
		var   toPiece = this.situationList[step - 1][vschess.i2s[this.getMoveByStep(step).substring(2, 4)]];

		// 播放将杀音效
		if (this.legalList.length === 0) {
			this.playSound("lose");
		}

		// 播放将军音效
		else if (vschess.checkThreat(this.situationList[this.getCurrentStep()])) {
			this.playSound("check");
		}

		// 播放炮吃子、普通吃子音效
		else if (toPiece > 1) {
			(fromPiece & 15) === 6 ? this.playSound("bomb") : this.playSound("eat");
		}

		// 禁止长打并且不可变着，按困毙处理
		else if (this.getBanRepeatLongThreat() && this.legalList.length <= this.repeatLongThreatMoveList.length) {
			this.playSound("lose");
		}

		// 播放移动棋子音效
		else {
			this.playSound("move");
		}
	}

	return this;
};

// 朗读着法
vschess.load.prototype.speakMove = function(move){
	if (!this.getSound()) {
		return this;
	}

	if (window.SpeechSynthesisUtterance && window.speechSynthesis) {
		var speech    = new SpeechSynthesisUtterance();
		speech.text   = move;
		speech.lang   = "zh-CN";
		speech.volume = this.getVolume() / 100;
		speechSynthesis.speak(speech);
	}
	else if (window.ActiveXObject) {
		vschess.TTS || (vschess.TTS = new ActiveXObject("Sapi.SpVoice"));
		vschess.TTS &&  vschess.TTS.Speak(move, 1);
	}

	return this;
};

// 设置音效状态
vschess.load.prototype.setSound = function(sound){
	this._.sound = !!sound;
	this.setConfigItemValue("sound", this._.sound);
	return this;
};

// 取得音效状态
vschess.load.prototype.getSound = function(){
	return this._.sound;
};

// 设置着法朗读状态
vschess.load.prototype.setSpeakMove = function(speakMove){
	this._.speakMove = !!speakMove;
	this.setConfigItemValue("speakMove", this._.speakMove);
	return this;
};

// 取得着法朗读状态
vschess.load.prototype.getSpeakMove = function(){
	return this._.speakMove;
};

// 设置音量大小
vschess.load.prototype.setVolume = function(volume){
	this._.volume = vschess.limit(volume, 0, 100);
	this.setConfigItemValue("volume", this._.volume);
	return this;
};

// 获取音量大小
vschess.load.prototype.getVolume = function(){
	return this._.volume;
};

// 创建标签
vschess.load.prototype.createTab = function(){
	this.tabArea = $('<div class="vschess-tab-area"></div>');
	this.DOM.children(".vschess-tab-area").remove();
	this.DOM.append(this.tabArea);
	this.createComment();
	this.createInfo   ();
	this.createExport ();
	this.createEdit   ();
	this.createConfig ();
	this.tabTitle = this.tabArea.children(".vschess-tab-title");
	this.tabBody  = this.tabArea.children(".vschess-tab-body" );
	return this;
};

// 显示指定标签
vschess.load.prototype.showTab = function(tabName){
	if (!~vschess.tabList.indexOf(tabName)) {
		return this;
	}

    this.tabTitle.removeClass("vschess-tab-title-current");
    this.tabBody.removeClass("vschess-tab-body-current");
    this.mobileCloseTab.removeClass("vschess-mobile-close-tab-current");
    this.mobileShowMoveList.removeClass("vschess-mobile-show-move-list-current");
    this.moveSelectList.removeClass("vschess-move-select-list-current");
    this.changeSelectTitle.removeClass("vschess-change-select-title-current");
    this.changeSelectList.removeClass("vschess-change-select-list-current");
    //this.formatBar.removeClass("vschess-format-bar-current");

    if (tabName === "board") {
        this.mobileCloseTab.addClass("vschess-mobile-close-tab-current");
    }
    else if (tabName === "move") {
        this.mobileShowMoveList.addClass("vschess-mobile-show-move-list-current");
        this.moveSelectList.addClass("vschess-move-select-list-current");
        this.changeSelectTitle.addClass("vschess-change-select-title-current");
        this.changeSelectList.addClass("vschess-change-select-list-current");
        //this.formatBar.addClass("vschess-format-bar-current");
    }
    else {
        this.tabTitle.filter(".vschess-tab-title-" + tabName).addClass("vschess-tab-title-current");
        this.tabBody .filter(".vschess-tab-body-"  + tabName).addClass("vschess-tab-body-current" );
    }

	return this;
};

// 棋盘对象转换为字符串信息
vschess.load.prototype.toString = function(){
	return this.getCurrentFen();
};

vschess.load.prototype.randomReview = function () {
  const currentStep = this.getCurrentStep();
  var currentNode = this.selectDefault(currentStep);

  let queue_todo = [[currentNode]];
  let queue_done = [];
  while (queue_todo.length > 0) {
    nodes = queue_todo.pop();
    lastnode = nodes[nodes.length - 1];
    if (lastnode.next.length == 0) {
      queue_done.push(nodes);
    } else {
      for (var i = 0; i < lastnode.next.length; i++) {
        queue_todo.push([...nodes, lastnode.next[i]]);
      }
    }
  }

  if (queue_done.length < 2) return;

  const index = Math.floor(Math.random() * queue_done.length);
  const randomNodes = queue_done[index];
  if (randomNodes.length < 2) return;

  for (var i = 1; i < randomNodes.length; i++) {
    if (this.setMoveDefaultAtNode(randomNodes[i].move, i + currentStep - 1)) {
      this.rebuildSituation().refreshBoard().refreshMoveSelectListNode();
    }
  }
};

// 程序转换为字符串信息
vschess.toString = function(){
	return "微思象棋播放器 V" + vschess.version + " https://www.xiaxiangqi.com/vschess/ Copyright © 2009-2023 Margin.Top 版权所有";
};

// 将 vschess 提升为全局变量，这样外部脚本就可以调用了
typeof window.vschess === "undefined" && (window.vschess = vschess);

})();