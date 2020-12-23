(function (global, factory) {
    typeof exports === 'object' && typeof module !== 'undefined' ? module.exports = factory() :
    typeof define === 'function' && define.amd ? define(factory) :
    (global.PathToolkit = factory());
}(this, (function () { 'use strict';

/**
 * @fileOverview PathToolkit evaluates string paths as property/index sequences within objects and arrays
 * @author Aaron Brown
 * @version 1.1.0
 */

// Parsing, tokeninzing, etc
// Some constants for convenience
var UNDEF = (function(u){return u;})();

// Static strings, assigned to aid code minification
var $WILDCARD     = '*';
var $UNDEFINED    = 'undefined';
var $STRING       = 'string';
var $PARENT       = 'parent';
var $ROOT         = 'root';
var $PLACEHOLDER  = 'placeholder';
var $CONTEXT      = 'context';
var $PROPERTY     = 'property';
var $COLLECTION   = 'collection';
var $EACH         = 'each';
var $SINGLEQUOTE  = 'singlequote';
var $DOUBLEQUOTE  = 'doublequote';
var $CALL         = 'call';
var $EVALPROPERTY = 'evalProperty';

/**
 * Tests whether a wildcard templates matches a given string.
 * ```javascript
 * var str = 'aaabbbxxxcccddd';
 * wildCardMatch('aaabbbxxxcccddd'); // true
 * wildCardMatch('*', str); // true
 * wildCardMatch('*', ''); // true
 * wildCardMatch('a*', str); // true
 * wildCardMatch('aa*ddd', str); // true
 * wildCardMatch('*d', str); // true
 * wildCardMatch('*a', str); // false
 * wildCardMatch('a*z', str); // false
 * ```
 * @private
 * @param  {String} template Wildcard pattern
 * @param  {String} str      String to match against wildcard pattern
 * @return {Boolean}          True if pattern matches string; False if not
 */
var wildCardMatch = function(template, str){
    var pos = template.indexOf($WILDCARD),
        parts = template.split($WILDCARD, 2),
        match = true;
    if (parts[0]){
        // If no wildcard present, return simple string comparison
        if (parts[0] === template){
            return parts[0] === str;
        }
        else {
            match = match && str.substr(0, parts[0].length) === parts[0];
        }
    }
    if (parts[1]){
        match = match && str.substr(-1*parts[1].length) === parts[1];
    }
    return match;
};

/**
 * Inspect input value and determine whether it is an Object or not.
 * Values of undefined and null will return "false", otherwise
 * must be of type "object" or "function".
 * @private
 * @param  {Object}  val Thing to examine, may be of any type
 * @return {Boolean}     True if thing is of type "object" or "function"
 */
var isObject = function(val){
    if (typeof val === $UNDEFINED || val === null) { return false;}
    return ( (typeof val === 'function') || (typeof val === 'object') );
};

/**
 * Inspect input value and determine whether it is an Integer or not.
 * Values of undefined and null will return "false".
 * @private
 * @param  {String}  val String to examine
 * @return {Boolean}     True if thing consists of at least one digit and only of digits (no . or ,)
 */
var digitsRegex = /^\d+$/;
var isDigits = function(val){
    return digitsRegex.test(val);
};

/**
 * Convert various values to true boolean `true` or `false`.
 * For non-string values, the native javascript idea of "true" will apply.
 * For string values, the words "true", "yes", and "on" will all return `true`.
 * All other strings return `false`. The string match is non-case-sensitive.
 * @private
 */
var truthify = function(val){
    var v;
    if (typeof val !== $STRING){
        return val && true; // Use native javascript notion of "truthy"
    }
    v = val.toUpperCase();
    if (v === 'TRUE' || v === 'YES' || v === 'ON'){
        return true;
    }
    return false;
};

/**
 * Using provided quote character as prefix and suffix, escape any instances
 * of the quote character within the string and return quote+string+quote.
 * The character defined as "singlequote" may be altered by custom options,
 * so a general-purpose function is needed to quote path segments correctly.
 * @private
 * @param  {String} q   Single-character string to use as quote character
 * @param  {String} str String to be quoted.
 * @return {String}     Original string, surrounded by the quote character, possibly modified internally if the quote character exists within the string.
 */
var quoteString = function(q, str){
    var qRegEx = new RegExp(q, 'g');
    return q + str.replace(qRegEx, '\\' + q) + q;
};

/**
 * PathToolkit base object. Includes all instance-specific data (options, cache)
 * as local variables. May be passed an options hash to pre-configure the
 * instance prior to use.
 * @constructor
 * @property {Object} options Optional. Collection of configuration settings for this instance of PathToolkit. See `setOptions` function below for detailed documentation.
 */
var PathToolkit = function(options){
    var _this = this,
        cache = {},
        opt = {},
        prefixList, separatorList, containerList, containerCloseList,
        propertySeparator,
        singlequote, doublequote,
        simplePathChars, simplePathRegEx,
        allSpecials, allSpecialsRegEx,
        escapedNonSpecialsRegEx,
        escapedQuotes,
        wildcardRegEx;

    /**
     * Several regular expressions are pre-compiled for use in path interpretation.
     * These expressions are built from the current syntax configuration, so they
     * must be re-built every time the syntax changes.
     * @private
     */
    var updateRegEx = function(){
        // Lists of special characters for use in regular expressions
        prefixList = Object.keys(opt.prefixes);
        separatorList = Object.keys(opt.separators);
        containerList = Object.keys(opt.containers);
        containerCloseList = containerList.map(function(key){ return opt.containers[key].closer; });

        propertySeparator = '';
        Object.keys(opt.separators).forEach(function(sep){ if (opt.separators[sep].exec === $PROPERTY){ propertySeparator = sep; } });
        singlequote = '';
        doublequote = '';
        Object.keys(opt.containers).forEach(function(sep){
            if (opt.containers[sep].exec === $SINGLEQUOTE){ singlequote = sep;}
            if (opt.containers[sep].exec === $DOUBLEQUOTE){ doublequote = sep;}
        });

        // Find all special characters except property separator (. by default)
        simplePathChars = '[\\\\' + [$WILDCARD].concat(prefixList).concat(separatorList).concat(containerList).join('\\').replace('\\'+propertySeparator, '') + ']';
        simplePathRegEx = new RegExp(simplePathChars);

        // Find all special characters, including backslash
        allSpecials = '[\\\\\\' + [$WILDCARD].concat(prefixList).concat(separatorList).concat(containerList).concat(containerCloseList).join('\\') + ']';
        allSpecialsRegEx = new RegExp(allSpecials, 'g');

        // Find all escaped special characters
        // escapedSpecialsRegEx = new RegExp('\\'+allSpecials, 'g');
        // Find all escaped non-special characters, i.e. unnecessary escapes
        escapedNonSpecialsRegEx = new RegExp('\\'+allSpecials.replace(/^\[/,'[^'));
        if (singlequote || doublequote){
            escapedQuotes = new RegExp('\\['+singlequote+doublequote+']', 'g');
        }
        else {
            escapedQuotes = '';
        }

        // Find wildcard character
        wildcardRegEx = new RegExp('\\'+$WILDCARD);
    };

    /**
     * Sets all the default options for interpreter behavior and syntax.
     * @private
     */
    var setDefaultOptions = function(){
        opt = opt || {};
        // Default settings
        opt.useCache = true;  // cache tokenized paths for repeated use
        opt.simple = false;   // only support dot-separated paths, no other special characters
        opt.force = false;    // create intermediate properties during `set` operation
        opt['defaultReturnVal'] = UNDEF;   // return undefined by default when path resolution fails

        // Default prefix special characters
        opt.prefixes = {
            '^': {
                'exec': $PARENT
            },
            '~': {
                'exec': $ROOT
            },
            '%': {
                'exec': $PLACEHOLDER
            },
            '@': {
                'exec': $CONTEXT
            }
        };
        // Default separator special characters
        opt.separators = {
            '.': {
                'exec': $PROPERTY
                },
            ',': {
                'exec': $COLLECTION
                },
            '<': {
                'exec': $EACH
            }
        };
        // Default container special characters
        opt.containers = {
            '[': {
                'closer': ']',
                'exec': $PROPERTY
                },
            '\'': {
                'closer': '\'',
                'exec': $SINGLEQUOTE
                },
            '"': {
                'closer': '"',
                'exec': $DOUBLEQUOTE
                },
            '(': {
                'closer': ')',
                'exec': $CALL
                },
            '{': {
                'closer': '}',
                'exec': $EVALPROPERTY
                }
        };
    };

    /**
     * Test string to see if it is surrounded by single- or double-quote, using the
     * current configuration definition for those characters. If no quote container
     * is defined, this function will return false since it's not possible to quote
     * the string if there are no quotes in the syntax. Also ignores escaped quote
     * characters.
     * @param {String} str The string to test for enclosing quotes
     * @return {Boolean} true = string is enclosed in quotes; false = not quoted
     */
    var isQuoted = function(str){
        var cleanStr = str.replace(escapedQuotes, '');
        var strLen = cleanStr.length;
        if (strLen < 2){ return false; }
        return  (cleanStr[0] === cleanStr[strLen - 1]) &&
                (cleanStr[0] === singlequote || cleanStr[0] === doublequote);
    };

    /**
     * Remove enclosing quotes from a string. The isQuoted function will determine
     * if any change is needed. If the string is quoted, we know the first and last
     * characters are quote marks, so simply do a string slice. If the input value is
     * not quoted, return the input value unchanged. Because isQuoted is used, if
     * no quote marks are defined in the syntax, this function will return the input value.
     * @param {String} str The string to un-quote
     * @return {String} The input string without any enclosing quote marks.
     */
    var stripQuotes = function(str){
        if (isQuoted(str)){
            return str.slice(1, -1);
        }
        return str;
    };

    /**
     * Scan input string from left to right, one character at a time. If a special character
     * is found (one of "separators", "containers", or "prefixes"), either store the accumulated
     * word as a token or else begin watching input for end of token (finding a closing character
     * for a container or the end of a collection). If a container is found, capture the substring
     * within the container and recursively call `tokenize` on that substring. Final output will
     * be an array of tokens. A complex token (not a simple property or index) will be represented
     * as an object carrying metadata for processing.
     * @private
     * @param  {String} str Path string
     * @return {Array}     Array of tokens found in the input path
     */
    var tokenize = function (str){
        var path = '',
            simplePath = true, // path is assumed "simple" until proven otherwise
            tokens = [],
            recur = [],
            mods = {},
            pathLength = 0,
            word = '',
            hasWildcard = false,
            doEach = false, // must remember the "each" operator into the following token
            subpath = '',
            i = 0,
            opener = '',
            closer = '',
            separator = '',
            collection = [],
            depth = 0,
            escaped = 0;

        if (opt.useCache && cache[str] !== UNDEF){ return cache[str]; }

        // Strip out any unnecessary escaping to simplify processing below
        path = str.replace(escapedNonSpecialsRegEx, '$&'.substr(1));
        pathLength = path.length;

        if (typeof str === $STRING && !simplePathRegEx.test(str)){
            tokens = path.split(propertySeparator);
            opt.useCache && (cache[str] = {t: tokens, simple: simplePath});
            return {t: tokens, simple: simplePath};
        }

        for (i = 0; i < pathLength; i++){
            // Skip escape character (`\`) and set "escaped" to the index value
            // of the character to be treated as a literal
            if (!escaped && path[i] === '\\'){
                // Next character is the escaped character
                escaped = i+1;
                i++;
            }
            // If a wildcard character is found, mark this token as having a wildcard
            if (path[i] === $WILDCARD) {
                hasWildcard = true;
            }
            // If we have already processed a container opener, treat this subpath specially
            if (depth > 0){
                // Is this character another opener from the same container? If so, add to
                // the depth level so we can match the closers correctly. (Except for quotes
                // which cannot be nested)
                // Is this character the closer? If so, back out one level of depth.
                // Be careful: quote container uses same character for opener and closer.
                !escaped && path[i] === opener && opener !== closer.closer && depth++;
                !escaped && path[i] === closer.closer && depth--;

                // While still inside the container, just add to the subpath
                if (depth > 0){
                    subpath += path[i];
                }
                // When we close off the container, time to process the subpath and add results to our tokens
                else {
                    // Handle subpath "[bar]" in foo.[bar],[baz] - we must process subpath and create a new collection
                    if (i+1 < pathLength && opt.separators[path[i+1]] && opt.separators[path[i+1]].exec === $COLLECTION){
                        if (subpath.length && closer.exec === $PROPERTY){
                            recur = stripQuotes(subpath);
                        }
                        else if (closer.exec === $SINGLEQUOTE || closer.exec === $DOUBLEQUOTE){
                            if (mods.has){
                                recur = {'w': subpath, 'mods': mods, 'doEach': doEach};
                                // tokens.push(word);
                                mods = {};
                                simplePath &= false;
                            }
                            else {
                                recur = subpath;
                                simplePath &= true;
                            }
                        }
                        else {
                            recur = tokenize(subpath);
                            if (recur === UNDEF){ return undefined; }
                            recur.exec = closer.exec;
                            recur.doEach = doEach;
                        }
                        // collection.push(closer.exec === $PROPERTY ? recur.t[0] : recur);
                        collection.push(recur);
                    }
                    // Handle subpath "[baz]" in foo.[bar],[baz] - we must process subpath and add to collection
                    else if (collection[0]){
                        if (subpath.length && closer.exec === $PROPERTY){
                            recur = stripQuotes(subpath);
                        }
                        else if (closer.exec === $SINGLEQUOTE || closer.exec === $DOUBLEQUOTE){
                            if (mods.has){
                                recur = {'w': subpath, 'mods': mods, 'doEach': doEach};
                                // tokens.push(word);
                                mods = {};
                                simplePath &= false;
                            }
                            else {
                                recur = subpath;
                                simplePath &= true;
                            }
                        }
                        else {
                            recur = tokenize(subpath);
                            if (recur === UNDEF){ return undefined; }
                            recur.exec = closer.exec;
                            recur.doEach = doEach;
                        }
                        collection.push(recur);
                        tokens.push({'tt':collection, 'doEach':doEach});
                        collection = [];
                        simplePath &= false;
                    }
                    // Simple property container is equivalent to dot-separated token. Just add this token to tokens.
                    else if (closer.exec === $PROPERTY){
                        recur = {t:[stripQuotes(subpath)]};
                        if (doEach){
                            tokens.push({'w':recur.t[0], 'mods':{}, 'doEach':true});
                            simplePath &= false;
                            doEach = false; // reset
                        }
                        else {
                            tokens.push(recur.t[0]);
                            simplePath &= true;
                        }
                    }
                    // Quoted subpath is all taken literally without token evaluation. Just add subpath to tokens as-is.
                    else if (closer.exec === $SINGLEQUOTE || closer.exec === $DOUBLEQUOTE){
                        if (mods.has){
                            word = {'w': subpath, 'mods': mods, 'doEach': doEach};
                            // tokens.push(word);
                            mods = {};
                            simplePath &= false;
                        }
                        else {
                            tokens.push(subpath);
                            simplePath &= true;
                        }
                    }
                    // Otherwise, create token object to hold tokenized subpath, add to tokens.
                    else {
                        if (subpath === ''){
                            recur = {t:[],simple:true};
                        }
                        else {
                            recur = tokenize(subpath);
                        }
                        if (recur === UNDEF){ return undefined; }
                        recur.exec = closer.exec;
                        recur.doEach = doEach;
                        tokens.push(recur);
                        simplePath &= false;
                    }
                    subpath = ''; // reset subpath
                }
            }
            // If a prefix character is found, store it in `mods` for later reference.
            // Must keep count due to `parent` prefix that can be used multiple times in one token.
            else if (!escaped && path[i] in opt.prefixes && opt.prefixes[path[i]].exec){
                mods.has = true;
                if (mods[opt.prefixes[path[i]].exec]) { mods[opt.prefixes[path[i]].exec]++; }
                else { mods[opt.prefixes[path[i]].exec] = 1; }
            }
            // If a separator is found, time to store the token we've been accumulating. If
            // this token had a prefix, we store the token as an object with modifier data.
            // If the separator is the collection separator, we must either create or add
            // to a collection for this token. For simple separator, we either add the token
            // to the token list or else add to the existing collection if it exists.
            else if (!escaped && opt.separators[path[i]] && opt.separators[path[i]].exec){
                separator = opt.separators[path[i]];
                if (!word && (mods.has || hasWildcard)){
                    // found a separator, after seeing prefixes, but no token word -> invalid
                    return undefined;
                }
                // This token will require special interpreter processing due to prefix or wildcard.
                if (word && (mods.has || hasWildcard || doEach)){
                    word = {'w': word, 'mods': mods, 'doEach': doEach};
                    mods = {};
                    simplePath &= false;
                }
                // word is a plain property or end of collection
                if (separator.exec === $PROPERTY || separator.exec === $EACH){
                    // we are gathering a collection, so add last word to collection and then store
                    if (collection[0] !== UNDEF){
                        word && collection.push(word);
                        tokens.push({'tt':collection, 'doEach':doEach});
                        collection = []; // reset
                        simplePath &= false;
                    }
                    // word is a plain property
                    else {
                        word && tokens.push(word);
                        simplePath &= true;
                    }
                    // If the separator is the "each" separtor, the following word will be evaluated differently.
                    // If it's not the "each" separator, then reset "doEach"
                    doEach = separator.exec === $EACH; // reset
                }
                // word is a collection
                else if (separator.exec === $COLLECTION){
                    word && collection.push(word);
                }
                word = ''; // reset
                hasWildcard = false; // reset
            }
            // Found a container opening character. A container opening is equivalent to
            // finding a separator, so "foo.bar" is equivalent to "foo[bar]", so apply similar
            // process as separator above with respect to token we have accumulated so far.
            // Except in case collections - path may have a collection of containers, so
            // in "foo[bar],[baz]", the "[bar]" marks the end of token "foo", but "[baz]" is
            // merely another entry in the collection, so we don't close off the collection token
            // yet.
            // Set depth value for further processing.
            else if (!escaped && opt.containers[path[i]] && opt.containers[path[i]].exec){
                closer = opt.containers[path[i]];
                if (word && (mods.has || hasWildcard || doEach)){
                    if (typeof word === 'string'){
                        word = {'w': word, 'mods': mods, 'doEach':doEach};
                    }
                    else {
                        word.mods = mods;
                        word.doEach = doEach;
                    }
                    mods = {};
                }
                if (collection[0] !== UNDEF){
                    // we are gathering a collection, so add last word to collection and then store
                    word && collection.push(word);
                }
                else {
                    // word is a plain property
                    word && tokens.push(word);
                    simplePath &= true;
                }
                opener = path[i];
                // 1) don't reset doEach for empty word because this is [foo]<[bar]
                // 2) don't reset doEach for opening Call because this is a,b<fn()
                if (word && opt.containers[opener].exec !== $CALL){
                    doEach = false;
                }
                word = '';
                hasWildcard = false;
                depth++;
            }
            // Otherwise, this is just another character to add to the current token
            else if (i < pathLength) {
                word += path[i];
            }

            // If current path index matches the escape index value, reset `escaped`
            if (i < pathLength && i === escaped){
                escaped = 0;
            }
        }

        // Path ended in an escape character
        if (escaped){
            return undefined;
        }

        // Add trailing word to tokens, if present
        if (typeof word === 'string' && word && (mods.has || hasWildcard || doEach)){
            word = {'w': word, 'mods': word.mods || mods, 'doEach': doEach};
            mods = {};
            simplePath &= false;
        }
        else if (word && mods.has){
            word.mods = mods;
        }
        // We are gathering a collection, so add last word to collection and then store
        if (collection[0] !== UNDEF){
            word && collection.push(word);
            tokens.push({'tt':collection, 'doEach':doEach});
            simplePath &= false;
        }
        // Word is a plain property
        else {
            word && tokens.push(word);
            simplePath &= true;
        }

        // depth != 0 means mismatched containers
        if (depth !== 0){ return undefined; }

        // If path was valid, cache the result
        opt.useCache && (cache[str] = {t: tokens, simple: simplePath});

        return {t: tokens, simple: simplePath};
    };

    /**
     * It is `resolvePath`'s job to traverse an object according to the tokens
     * derived from the keypath and either return the value found there or set
     * a new value in that location.
     * The tokens are a simple array and `reoslvePath` loops through the list
     * with a simple "while" loop. A token may itself be a nested token array,
     * which is processed through recursion.
     * As each successive value is resolved within `obj`, the current value is
     * pushed onto the "valueStack", enabling backward references (upwards in `obj`)
     * through path prefixes like "<" for "parent" and "~" for "root". The loop
     * short-circuits by returning `undefined` if the path is invalid at any point,
     * except in `set` scenario with `force` enabled.
     * @private
     * @param  {Object} obj        The data object to be read/written
     * @param  {String} path       The keypath which `resolvePath` will evaluate against `obj`. May be a pre-compiled Tokens set instead of a string.
     * @param  {Any} newValue   The new value to set at the point described by `path`. Undefined if used in `get` scenario.
     * @param  {Array} args       Array of extra arguments which may be referenced by placeholders. Undefined if no extra arguments were given.
     * @param  {Array} valueStack Stack of object contexts accumulated as the path tokens are processed in `obj`
     * @return {Any}            In `get`, returns the value found in `obj` at `path`. In `set`, returns the new value that was set in `obj`. If `get` or `set` are nto successful, returns `undefined`
     */
    var resolvePath = function (obj, path, newValue, args, valueStack){
        var change = newValue !== UNDEF, // are we setting a new value?
            tk = [],
            tkLength = 0,
            tkLastIdx = 0,
            valueStackLength = 1,
            i = 0, j = 0,
            prev = obj,
            curr = '',
            currLength = 0,
            eachLength = 0,
            wordCopy = '',
            contextProp,
            idx = 0,
            context = obj,
            ret,
            newValueHere = false,
            placeInt = 0,
            prop = '',
            callArgs;

        // For String path, either fetch tokens from cache or from `tokenize`.
        if (typeof path === $STRING){
            if (opt.useCache && cache[path]) { tk = cache[path].t; }
            else {
                tk = tokenize(path);
                if (tk === UNDEF){ return undefined; }
                tk = tk.t;
            }
        }
        // For a non-string, assume a pre-compiled token array
        else {
            tk = path.t ? path.t : [path];
        }

        tkLength = tk.length;
        if (tkLength === 0) { return undefined; }
        tkLastIdx = tkLength - 1;

        // valueStack will be an array if we are within a recursive call to `resolvePath`
        if (valueStack){
            valueStackLength = valueStack.length;
        }
        // On original entry to `resolvePath`, initialize valueStack with the base object.
        // valueStackLength was already initialized to 1.
        else {
            valueStack = [obj];
        }

        // Converted Array.reduce into while loop, still using "prev", "curr", "idx"
        // as loop values
        while (prev !== UNDEF && idx < tkLength){
            curr = tk[idx];

            // If we are setting a new value and this token is the last token, this
            // is the point where the new value must be set.
            newValueHere = (change && (idx === tkLastIdx));

            // Handle most common simple path scenario first
            if (typeof curr === $STRING){
                // If we are setting...
                if (change){
                    // If this is the final token where the new value goes, set it
                    if (newValueHere){
                        context[curr] = newValue;
                        if (context[curr] !== newValue){ return undefined; } // new value failed to set
                    }
                    // For earlier tokens, create object properties if "force" is enabled
                    else if (opt.force && typeof context[curr] === 'undefined') {
                        context[curr] = {};
                    }
                }
                // Return value is assigned as value of this object property
                ret = context[curr];

                // This basic structure is repeated in other scenarios below, so the logic
                // pattern is only documented here for brevity.
            }
            else {
                if (curr === UNDEF){
                    ret = undefined;
                }
                else if (curr.tt){
                    // Call resolvePath again with base value as evaluated value so far and
                    // each element of array as the path. Concat all the results together.
                    ret = [];
                    if (curr.doEach){
                        if (!Array.isArray(context)){
                            return undefined;
                        }
                        j = 0;
                        eachLength = context.length;

                        // Path like Array->Each->Array requires a nested for loop
                        // to process the two array layers.
                        while(j < eachLength){
                            i = 0;
                            ret.push([]);
                            currLength = curr.tt.length;
                            while(i < currLength){
                                curr.tt[i].doEach = false; // This is a hack, don't know how else to disable "doEach" for collection members
                                if (newValueHere){
                                    contextProp = resolvePath(context[j], curr.tt[i], newValue, args, valueStack);
                                }
                                else if (typeof curr.tt[i] === 'string'){
                                    contextProp = context[j][curr.tt[i]];
                                }
                                else {
                                    contextProp = resolvePath(context[j], curr.tt[i], undefined, args, valueStack);
                                }
                                if (contextProp === UNDEF) { return undefined; }

                                if (newValueHere){
                                    if (curr.tt[i].t && curr.tt[i].exec === $EVALPROPERTY){
                                        context[j][contextProp] = newValue;
                                    } else {
                                        ret[j].push(contextProp);
                                    }
                                }
                                else {
                                    if (curr.tt[i].t && curr.tt[i].exec === $EVALPROPERTY){
                                        ret[j].push(context[j][contextProp]);
                                    } else {
                                        ret[j].push(contextProp);
                                    }
                                }
                                i++;
                            }
                            j++;
                        }
                    }
                    else {
                        i = 0;
                        currLength = curr.tt.length;
                        while(i < currLength){
                            if (newValueHere){
                                contextProp = resolvePath(context, curr.tt[i], newValue, args, valueStack);
                            }
                            else if (typeof curr.tt[i] === 'string'){
                                contextProp = context[curr.tt[i]];
                            }
                            else {
                                contextProp = resolvePath(context, curr.tt[i], undefined, args, valueStack);
                            }
                            if (contextProp === UNDEF) { return undefined; }

                            if (newValueHere){
                                if (curr.tt[i].t && curr.tt[i].exec === $EVALPROPERTY){
                                    context[contextProp] = newValue;
                                } else {
                                    ret.push(contextProp);
                                }
                            }
                            else {
                                if (curr.tt[i].t && curr.tt[i].exec === $EVALPROPERTY){
                                    ret.push(context[contextProp]);
                                } else {
                                    ret.push(contextProp);
                                }
                            }
                            i++;
                        }
                    }
                }
                else if (curr.w){
                    // this word token has modifiers
                    wordCopy = curr.w;
                    if (curr.mods.has){
                        if (curr.mods.parent){
                            // modify current context, shift upwards in base object one level
                            context = valueStack[valueStackLength - 1 - curr.mods.parent];
                            if (context === UNDEF) { return undefined; }
                        }
                        if (curr.mods.root){
                            // Reset context and valueStack, start over at root in this context
                            context = valueStack[0];
                            valueStack = [context];
                            valueStackLength = 1;
                        }
                        if (curr.mods.placeholder){
                            placeInt = wordCopy - 1;
                            if (args[placeInt] === UNDEF){ return undefined; }
                            // Force args[placeInt] to String, won't attempt to process
                            // arg of type function, array, or plain object
                            wordCopy = args[placeInt].toString();
                        }
                    }

                    // doEach option means to take all values in context (must be an array), apply
                    // "curr" to each one, and return the new array. Operates like Array.map.
                    if (curr.doEach){
                        if (!Array.isArray(context)){
                            return undefined;
                        }
                        ret = [];
                        i = 0;
                        eachLength = context.length;
                        while(i < eachLength){
                            // "context" modifier ("@" by default) replaces current context with a value from
                            // the arguments.
                            if (curr.mods.context){
                                if (isDigits(wordCopy)){
                                    placeInt = wordCopy - 1;
                                    if (args[placeInt] === UNDEF){ return undefined; }
                                    // Force args[placeInt] to String, won't atwordCopyt to process
                                    // arg of type function, array, or plain object
                                    ret.push(args[placeInt]);
                                }
                                else {
                                    ret = wordCopy;
                                }
                            }
                            else {
                                // Repeat basic string property processing with word and modified context
                                if (context[i][wordCopy] !== UNDEF) {
                                    if (newValueHere){ context[i][wordCopy] = newValue; }
                                    ret.push(context[i][wordCopy]);
                                }
                                else if (typeof context[i] === 'function'){
                                    ret.push(wordCopy);
                                }
                                // Plain property tokens are listed as special word tokens whenever
                                // a wildcard is found within the property string. A wildcard in a
                                // property causes an array of matching properties to be returned,
                                // so loop through all properties and evaluate token for every
                                // property where `wildCardMatch` returns true.
                                else if (wildcardRegEx.test(wordCopy)){
                                    ret.push([]);
                                    for (prop in context[i]){
                                        if (wildCardMatch(wordCopy, prop)){
                                            if (newValueHere){ context[i][prop] = newValue; }
                                            ret[i].push(context[i][prop]);
                                        }
                                    }
                                }
                                else { return undefined; }
                            }
                            i++;
                        }
                    }
                    else {
                        // "context" modifier ("@" by default) replaces current context with a value from
                        // the arguments.
                        if (curr.mods.context){
                            if (isDigits(wordCopy)){
                                placeInt = wordCopy - 1;
                                if (args[placeInt] === UNDEF){ return undefined; }
                                // Force args[placeInt] to String, won't atwordCopyt to process
                                // arg of type function, array, or plain object
                                ret = args[placeInt];
                            } else {
                                ret = wordCopy;
                            }
                        }
                        else {
                            // Repeat basic string property processing with word and modified context
                            if (context[wordCopy] !== UNDEF) {
                                if (newValueHere){ context[wordCopy] = newValue; }
                                ret = context[wordCopy];
                            }
                            else if (typeof context === 'function'){

                                ret = wordCopy;
                            }
                            // Plain property tokens are listed as special word tokens whenever
                            // a wildcard is found within the property string. A wildcard in a
                            // property causes an array of matching properties to be returned,
                            // so loop through all properties and evaluate token for every
                            // property where `wildCardMatch` returns true.
                            else if (wildcardRegEx.test(wordCopy)){
                                ret = [];
                                for (prop in context){
                                    if (wildCardMatch(wordCopy, prop)){
                                        if (newValueHere){ context[prop] = newValue; }
                                        ret.push(context[prop]);
                                    }
                                }
                            }
                            else { return undefined; }
                        }
                    }
                }
                // Eval Property tokens operate on a temporary context created by
                // recursively calling `resolvePath` with a copy of the valueStack.
                else if (curr.exec === $EVALPROPERTY){
                    if (curr.doEach){
                        if (!Array.isArray(context)){
                            return undefined;
                        }
                        ret = [];
                        i = 0;
                        eachLength = context.length;
                        while(i < eachLength){
                            if (curr.simple){
                                if (newValueHere){
                                    context[i][_this.get(context[i], {t:curr.t, simple:true})] = newValue;
                                }
                                ret.push(context[i][_this.get(context[i], {t:curr.t, simple:true})]);
                            }
                            else {
                                if (newValueHere){
                                    context[i][resolvePath(context[i], curr, UNDEF, args, valueStack)] = newValue;
                                }
                                ret.push(context[i][resolvePath(context[i], curr, UNDEF, args, valueStack)]);
                            }
                            i++;
                        }
                    }
                    else {
                        if (curr.simple){
                            if (newValueHere){
                                context[_this.get(context, {t: curr.t, simple:true})] = newValue;
                            }
                            ret = context[_this.get(context, {t:curr.t, simple:true})];
                        }
                        else {
                            if (newValueHere){
                                context[resolvePath(context, curr, UNDEF, args, valueStack)] = newValue;
                            }
                            ret = context[resolvePath(context, curr, UNDEF, args, valueStack)];
                        }
                    }
                }
                // Functions are called using `call` or `apply`, depending on the state of
                // the arguments within the ( ) container. Functions are executed with "this"
                // set to the context immediately prior to the function in the stack.
                // For example, "a.b.c.fn()" is equivalent to obj.a.b.c.fn.call(obj.a.b.c)
                else if (curr.exec === $CALL){
                    if (curr.doEach){
                        if (!Array.isArray(valueStack[valueStackLength - 2])){
                            return undefined;
                        }
                        ret = [];
                        i = 0;
                        eachLength = context.length;
                        while(i < eachLength){
                            // If function call has arguments, process those arguments as a new path
                            if (curr.t && curr.t.length){
                                callArgs = resolvePath(context, curr, UNDEF, args, valueStack);
                                if (callArgs === UNDEF){
                                    ret.push(context[i].apply(valueStack[valueStackLength - 2][i]));
                                }
                                else if (Array.isArray(callArgs)){
                                    ret.push(context[i].apply(valueStack[valueStackLength - 2][i], callArgs));
                                }
                                else {
                                    ret.push(context[i].call(valueStack[valueStackLength - 2][i], callArgs));
                                }
                            }
                            else {
                                ret.push(context[i].call(valueStack[valueStackLength - 2][i]));
                            }
                            i++;
                        }
                    }
                    else {
                        // If function call has arguments, process those arguments as a new path
                        if (curr.t && curr.t.length){
                            if (curr.simple){
                                callArgs = _this.get(context, curr);
                            }
                            else {
                                callArgs = resolvePath(context, curr, UNDEF, args, valueStack);
                            }
                            if (callArgs === UNDEF){
                                ret = context.apply(valueStack[valueStackLength - 2]);
                            }
                            else if (Array.isArray(callArgs)){
                                ret = context.apply(valueStack[valueStackLength - 2], callArgs);
                            }
                            else {
                                ret = context.call(valueStack[valueStackLength - 2], callArgs);
                            }
                        }
                        else {
                            ret = context.call(valueStack[valueStackLength - 2]);
                        }
                    }
                }
            }
            // Add the return value to the stack in case we must loop again.
            // Recursive calls pass the same valueStack array around, but we don't want to
            // push entries on the stack inside a recursion, so instead use fixed array
            // index references based on what **this** execution knows the valueStackLength
            // should be. That way, if a recursion adds new elements, and then we back out,
            // this context will remember the old stack length and will merely overwrite
            // those added entries, ignoring that they were there in the first place.
            valueStack[valueStackLength++] = ret;
            context = ret;
            prev = ret;
            idx++;
        }
        return context;
    };

    /**
     * Simplified path evaluation heavily optimized for performance when
     * processing paths with only property names or indices and separators.
     * If the path can be correctly processed with "path.split(separator)",
     * this function will do so. Any other special characters found in the
     * path will cause the path to be evaluated with the full `resolvePath`
     * function instead.
     * @private
     * @param  {Object} obj        The data object to be read/written
     * @param  {String} path       The keypath which `resolvePath` will evaluate against `obj`.
     * @param  {Any} newValue   The new value to set at the point described by `path`. Undefined if used in `get` scenario.
     * @return {Any}            In `get`, returns the value found in `obj` at `path`. In `set`, returns the new value that was set in `obj`. If `get` or `set` are nto successful, returns `undefined`
     */
    var quickResolveString = function(obj, path, newValue){
        var change = newValue !== UNDEF,
            tk = [],
            i = 0,
            tkLength = 0;

        tk = path.split(propertySeparator);
        opt.useCache && (cache[path] = {t: tk, simple: true});
        tkLength = tk.length;
        while (obj !== UNDEF && i < tkLength && !isPrototypePolluted(tk[i])){
            if (tk[i] === ''){ return undefined; }
            else if (change){
                if (i === tkLength - 1){
                    obj[tk[i]] = newValue;
                }
                // For arrays, test current context against undefined to avoid parsing this segment as a number.
                // For anything else, use hasOwnProperty.
                else if (opt.force && typeof obj[tk[i]] === 'undefined') {
                    obj[tk[i]] = {};
                }
            }
            obj = obj[tk[i++]];
        }
        return obj;
    };

    /**
     * Simplified path evaluation heavily optimized for performance when
     * processing array of simple path tokens (plain property names).
     * This function is essentially the same as `quickResolveString` except
     * `quickResolveTokenArray` does nto need to execute path.split.
     * @private
     * @param  {Object} obj        The data object to be read/written
     * @param  {Array} tk       The token array which `resolvePath` will evaluate against `obj`.
     * @param  {Any} newValue   The new value to set at the point described by `path`. Undefined if used in `get` scenario.
     * @return {Any}            In `get`, returns the value found in `obj` at `path`. In `set`, returns the new value that was set in `obj`. If `get` or `set` are nto successful, returns `undefined`
     */
    var quickResolveTokenArray = function(obj, tk, newValue){
        var change = newValue !== UNDEF,
            i = 0,
            tkLength = tk.length;

        while (obj != null && i < tkLength){
            if (tk[i] === ''){ return undefined; }
            else if (change){
                if (i === tkLength - 1){
                    obj[tk[i]] = newValue;
                }
                // For arrays, test current context against undefined to avoid parsing this segment as a number.
                // For anything else, use hasOwnProperty.
                else if (opt.force && typeof obj[tk[i]] === 'undefined') {
                    obj[tk[i]] = {};
                }
            }
            obj = obj[tk[i++]];
        }
        return obj;
    };

    /**
     * Searches an object or array for a value, accumulating the keypath to the value along
     * the way. Operates in a recursive way until either all keys/indices have been
     * exhausted or a match is found. Return value "true" means "keep scanning", "false"
     * means "stop now". If a match is found, instead of returning a simple "false", a
     * callback function (savePath) is called which will decide whether or not to continue
     * the scan. This allows the function to find one instance of value or all instances,
     * based on logic in the callback.
     * @private
     * @param {Object} obj    The data object to scan
     * @param {Any} val The value we are looking for within `obj`
     * @param {Function} savePath Callback function which will store accumulated paths and indicate whether to continue
     * @param {String} path Accumulated keypath; undefined at first, populated in recursive calls
     * @param {Function} isCircularCb Callback function which return true if this object has circular ancestry, used by `findSafe()`
     * @return {Boolean} Indicates whether scan process should continue ("true"->yes, "false"->no)
     */
    var scanForValue = function(obj, val, savePath, path, isCircularCb){
        var i, len, more, keys, prop;

        if (typeof path === $UNDEFINED){
            path = '';
        }
        else if (typeof isCircularCb !== $UNDEFINED){
            if (isCircularCb(obj, path)){
                throw new Error('Circular object provided. Path at "' + path + '" makes a loop.');
            }
        }

        // If we found the value we're looking for
        if (obj === val){
            return savePath(path); // Save the accumulated path, ask whether to continue
        }
        // This object is an array, so examine each index separately
        else if (Array.isArray(obj)){
            len = obj.length;
            for(i = 0; i < len; i++){
              more = scanForValue(obj[i], val, savePath, path === '' ? i : path + propertySeparator + i, isCircularCb);
                // Call `scanForValue` recursively
                // Halt if that recursive call returned "false"
                if (!more){ return; }
            }
            return true; // keep looking
        }
        // This object is an object, so examine each local property separately
        else if (isObject(obj)) {
            keys = Object.keys(obj);
            len = keys.length;
            if (len > 1){ keys = keys.sort(); } // Force order of object keys to produce repeatable results
            for (i = 0; i < len; i++){
                if (obj.hasOwnProperty(keys[i])){
                    prop = keys[i];
                    // Property may include the separator character or some other special character,
                    // so quote this path segment and escape any separators within.
                    if (allSpecialsRegEx.test(prop)){
                        prop = quoteString(singlequote, prop);
                    }
                    more = scanForValue(obj[keys[i]], val, savePath, path === '' ? prop : path + propertySeparator + prop, isCircularCb);
                    if (!more){ return; }
                }
            }
            return true; // keep looking
        }
        // Leaf node (string, number, character, boolean, etc.), but didn't match
        return true; // keep looking
    };

    /**
     * Check if trying to set magic attributes.
     * @private
     * @param {String} key 
     * @return {Boolean}
     */
    var isPrototypePolluted = function(key) {
        return ['__proto__', 'constructor', 'prototype'].includes(key)
    };

    /**
     * Get tokenized representation of string keypath.
     * @public
     * @param {String} path Keypath
     * @return {Object} Object including the array of path tokens and a boolean indicating "simple". Simple token sets have no special operators or nested tokens, only a plain array of strings for fast evaluation.
     */
    _this.getTokens = function(path){
        var tokens = tokenize(path);
        if (typeof tokens === $UNDEFINED){ return undefined; }
        return tokens;
    };

    /**
     * Informs whether the string path has valid syntax. The path is NOT evaluated against a
     * data object, only the syntax is checked.
     * @public
     * @param {String} path Keypath
     * @return {Boolean} valid syntax -> "true"; not valid -> "false"
     */
    _this.isValid = function(path){
        return typeof tokenize(path) !== $UNDEFINED;
    };

    /**
     * Escapes any special characters found in the input string using backslash, preventing
     * these characters from causing unintended processing by PathToolkit. This function
     * DOES respect the current configured syntax, even if it has been altered from the default.
     * @public
     * @param {String} segment Segment of a keypath
     * @return {String} The original segment string with all PathToolkit special characters prepended with "\"
     */
    _this.escape = function(segment){
        return segment.replace(allSpecialsRegEx, '\\$&');
    };

    /**
     * Evaluates keypath in object and returns the value found there, if available. If the path
     * does not exist in the provided data object, returns `undefined` (this return value is
     * configurable in options, see `setDefaultReturnVal` below). For "simple" paths, which
     * don't include any operations beyond property separators, optimized resolvers will be used
     * which are more lightweight than the full-featured `resolvePath`.
     * @public
     * @param {Any} obj Source data object
     * @param {String} path Keypath to evaluate within "obj". Also accepts token array in place of a string path.
     * @return {Any} If the keypath exists in "obj", return the value at that location; If not, return `undefined`.
     */
    _this.get = function (obj, path){
        var i = 0,
            returnVal,
            len = arguments.length,
            args;
        // For string paths, first see if path has already been cached and if the token set is simple. If
        // so, we can use the optimized token array resolver using the cached token set.
        // If there is no cached entry, use RegEx to look for special characters apart from the separator.
        // If none are found, we can use the optimized string resolver.
        if (typeof path === $STRING){
            if (opt.useCache && cache[path] && cache[path].simple){
                returnVal = quickResolveTokenArray(obj, cache[path].t);
            }
            else if (!simplePathRegEx.test(path)){
                returnVal = quickResolveString(obj, path);
            }
            // If we made it this far, the path is complex and may include placeholders. Gather up any
            // extra arguments and call the full `resolvePath` function.
            else {
                args = [];
                if (len > 2){
                    for (i = 2; i < len; i++) { args[i-2] = arguments[i]; }
                }
                returnVal = resolvePath(obj, path, undefined, args);
            }
        }
        // For array paths (pre-compiled token sets), check for simplicity so we can use the optimized resolver.
        else if (Array.isArray(path.t) && path.simple){
            returnVal = quickResolveTokenArray(obj, path.t);
        }
        // If we made it this far, the path is complex and may include placeholders. Gather up any
        // extra arguments and call the full `resolvePath` function.
        else {
            args = [];
            if (len > 2){
                for (i = 2; i < len; i++) { args[i-2] = arguments[i]; }
            }
            returnVal = resolvePath(obj, path, undefined, args);
        }

        return returnVal === UNDEF ? opt.defaultReturnVal : returnVal;
    };

    /**
     * Evaluates keypath in object and returns the value found there, if available. If the path
     * does not exist in the provided data object, returns default value as provided in arguments.
     * For "simple" paths, which don't include any operations beyond property separators, optimized
     * resolvers will be used which are more lightweight than the full-featured `resolvePath`.
     * @public
     * @param {Any} obj Source data object
     * @param {String} path Keypath to evaluate within "obj". Also accepts token array in place of a string path.
     * @param {Any} defaultReturnVal Value to return if "get" results in undefined.
     * @return {Any} If the keypath exists in "obj", return the value at that location; If not, return value from "defaultReturnVal".
     */
    _this.getWithDefault = function (obj, path, defaultReturnVal){
        var i = 0,
            returnVal,
            len = arguments.length,
            args = [ obj, path ];

        // Code below duplicates "get" method above rather than simply executing "get" and customizing
        // the return value because "get" may have failed to resolve and returned a non-undefined value
        // due to an instance option, options.defaultReturnVal. In that case, this method can't know
        // whether the non-undefined return value was the actual value at that path, or was returned
        // due to path resolution failure. To be safe, therefore, the "get" logic is duplicated but
        // the defaultReturnVal argument is used in place of the instance option in case of failure.

        // For string paths, first see if path has already been cached and if the token set is simple. If
        // so, we can use the optimized token array resolver using the cached token set.
        // If there is no cached entry, use RegEx to look for special characters apart from the separator.
        // If none are found, we can use the optimized string resolver.
        if (typeof path === $STRING){
            if (opt.useCache && cache[path] && cache[path].simple){
                returnVal = quickResolveTokenArray(obj, cache[path].t);
            }
            else if (!simplePathRegEx.test(path)){
                returnVal = quickResolveString(obj, path);
            }
            // If we made it this far, the path is complex and may include placeholders. Gather up any
            // extra arguments and call the full `resolvePath` function.
            else {
                args = [];
                if (len > 3){
                    for (i = 3; i < len; i++) { args[i-3] = arguments[i]; }
                }
                returnVal = resolvePath(obj, path, undefined, args);
            }
        }
        // For array paths (pre-compiled token sets), check for simplicity so we can use the optimized resolver.
        else if (Array.isArray(path.t) && path.simple){
            returnVal = quickResolveTokenArray(obj, path.t);
        }
        // If we made it this far, the path is complex and may include placeholders. Gather up any
        // extra arguments and call the full `resolvePath` function.
        else {
            args = [];
            if (len > 3){
                for (i = 3; i < len; i++) { args[i-3] = arguments[i]; }
            }
            returnVal = resolvePath(obj, path, undefined, args);
        }

        return returnVal === UNDEF ? defaultReturnVal : returnVal;
    };

    /**
     * Evaluates a keypath in object and sets a new value at the point described in the keypath. If
     * "force" is disabled, the full path must exist up to the final property, which may be created
     * by the set operation. If "force" is enabled, any missing intermediate properties will be created
     * in order to set the value on the final property. If `set` succeeds, returns "true", otherwise "false".
     * @public
     * @param {Any} obj Source data object
     * @param {String} path Keypath to evaluate within "obj". Also accepts token array in place of a string path.
     * @param {Any} val New value to set at the location described in "path"
     * @return {Boolean} "true" if the set operation succeeds; "false" if it does not succeed
     */
    _this.set = function(obj, path, val){
        var i = 0,
            len = arguments.length,
            args,
            ref,
            done = false;

        // Path resolution follows the same logic as `get` above, with one difference: `get` will
        // abort by returning the value as soon as it's found. `set` does not abort so the if-else
        // structure is slightly different to dictate when/if the final case should execute.
        if (typeof path === $STRING){
            if (opt.useCache && cache[path] && cache[path].simple){
                ref = quickResolveTokenArray(obj, cache[path].t, val);
                done |= true;
            }
            else if (!simplePathRegEx.test(path)){
                ref = quickResolveString(obj, path, val);
                done |= true;
            }
        }
        else if (Array.isArray(path.t) && path.simple){
            ref = quickResolveTokenArray(obj, path.t, val);
            done |= true;
        }

        // Path was (probably) a string and it contained complex path characters
        if (!done) {
            if (len > 3){
                args = [];
                for (i = 3; i < len; i++) { args[i-3] = arguments[i]; }
            }
            ref = resolvePath(obj, path, val, args);
        }

        // `set` can set a new value in multiple places if the final path segment is an array.
        // If any of those value assignments fail, `set` will return "false" indicating failure.
        if (Array.isArray(ref)){
            return ref.indexOf(undefined) === -1;
        }
        return ref !== UNDEF;
    };

    /**
     * Locate a value within an object or array. This is the publicly exposed interface to the
     * private `scanForValue` function defined above.
     * @public
     * @param {Any} obj Source data object
     * @param {Any} val The value to search for within "obj"
     * @param {String} oneOrMany Optional; If missing or "one", `find` will only return the first valid path. If "onOrMany" is any other string, `find` will scan the full object looking for all valid paths to all cases where "val" appears.
     * @return {Array} Array of keypaths to "val" or `undefined` if "val" is not found.
     */
    _this.find = function(obj, val, oneOrMany){
        var foundPaths = [];
        // savePath is the callback which will accumulate any found paths in a local array
        var savePath = function(path){
            foundPaths.push(path);
            if(!oneOrMany || oneOrMany === 'one'){
                return false; // stop scanning for value
            }
            return true; // keep scanning for value elsewhere in object
        };
        scanForValue(obj, val, savePath);
        if(!oneOrMany || oneOrMany === 'one'){
            return foundPaths.length > 0 ? foundPaths[0] : undefined;
        }
        return foundPaths.length > 0 ? foundPaths : undefined;
    };

    /**
     * Locate a value within an object or array. During scan, protect against loop references.
     * This is the publicly exposed interface to the private `scanForValue` function defined above.
     * @public
     * @param {Any} obj Source data object
     * @param {Any} val The value to search for within "obj"
     * @param {String} oneOrMany Optional; If missing or "one", `find` will only return the first valid path. If "onOrMany" is any other string, `find` will scan the full object looking for all valid paths to all cases where "val" appears.
     * @return {Array} Array of keypaths to "val" or `undefined` if "val" is not found.
     */
    _this.findSafe = function(obj, val, oneOrMany){
        var foundPaths = [];
        // savePath is the callback which will accumulate any found paths in a local array
        // variable.
        var savePath = function(path){
            foundPaths.push(path);
            if(!oneOrMany || oneOrMany === 'one'){
                return false; // stop scanning for value
            }
            return true; // keep scanning for value elsewhere in object
        };
        // isCircular is a callback that will test if this object also exists
        // in an ancestor path, indicating a circular reference.
        var isCircular = function(ref, path){
            var tokens = _this.getTokens(path);
            // Walk up the ancestor chain checking for equality with current object
            while(tokens.t.pop()){
                if(_this.get(obj, tokens) === ref){
                    return true;
                }
            }
            return false;
        };
        scanForValue(obj, val, savePath, UNDEF, isCircular);
        if(!oneOrMany || oneOrMany === 'one'){
            return foundPaths.length > 0 ? foundPaths[0] : undefined;
        }
        return foundPaths.length > 0 ? foundPaths : undefined;
    };

    /**
     * For a given special character group (e.g., separators) and character type (e.g., "property"),
     * replace an existing separator with a new character. This creates a new special character for
     * that purpose anwithin the character group and removes the old one. Also takes a "closer" argument
     * for cases where the special character is a container set.
     * @private
     * @param {Object} optionGroup Reference to current configuration for a certain type of special characters
     * @param {String} charType The type of special character to be replaced
     * @param {String} val New special character string
     * @param {String} closer Optional; New special character closer string, only used for "containers" group
     */
    var updateOptionChar = function(optionGroup, charType, val, closer){
        var oldVal = '';
        Object.keys(optionGroup).forEach(function(str){ if (optionGroup[str].exec === charType){ oldVal = str; } });

        delete optionGroup[oldVal];
        optionGroup[val] = {exec: charType};
        if (closer){ optionGroup[val].closer = closer; }
    };

    /**
     * Sets "simple" syntax in special character groups. This syntax only supports a separator
     * character and no other operators. A custom separator may be provided as an argument.
     * @private
     * @param {String} sep Optional; Separator string. If missing, the default separator (".") is used.
     */
    var setSimpleOptions = function(sep){
        var sepOpts = {};
        if (!(typeof sep === $STRING && sep.length === 1)){
            sep = '.';
        }
        sepOpts[sep] = {exec: $PROPERTY};
        opt.prefixes = {};
        opt.containers = {};
        opt.separators = sepOpts;
    };

    /**
     * Alter PathToolkit configuration. Takes an options hash which may include
     * multiple settings to change at once. If the path syntax is changed by
     * changing special characters, the cache is wiped. Each option group is
     * REPLACED by the new option group passed in. If an option group is not
     * included in the options hash, it is not changed.
     * @public
     * @param {Object} options Option hash. For sample input, see `setDefaultOptions` above.
     */
    _this.setOptions = function(options){
        if (options.prefixes){
            opt.prefixes = options.prefixes;
            cache = {};
        }
        if (options.separators){
            opt.separators = options.separators;
            cache = {};
        }
        if (options.containers){
            opt.containers = options.containers;
            cache = {};
        }
        if (typeof options.cache !== $UNDEFINED){
            opt.useCache = !!options.cache;
        }
        if (typeof options.simple !== $UNDEFINED){
            var tempCache = opt.useCache; // preserve these two options after "setDefaultOptions"
            var tempForce = opt.force;
            var tempDefaultReturnVal = opt.defaultReturnVal;

            opt.simple = truthify(options.simple);
            if (opt.simple){
                setSimpleOptions();
            }
            else {
                setDefaultOptions();
                opt.useCache = tempCache;
                opt.force = tempForce;
            }
            cache = {};
        }
        if (typeof options.force !== $UNDEFINED){
            opt.force = truthify(options.force);
        }
        // The default return value may be set to undefined, which
        // makes testing for this option more tricky.
        if (Object.keys(options).includes('defaultReturnVal')){
            opt['defaultReturnVal'] = options.defaultReturnVal;
        }
        updateRegEx();
    };

    /**
     * Sets use of keypath cache to enabled or disabled, depending on input value.
     * @public
     * @param {Any} val Value which will be interpreted as a boolean using `truthify`. "true" will enable cache; "false" will disable.
     */
    _this.setCache = function(val){
        opt.useCache = truthify(val);
    };
    /**
     * Enables use of keypath cache.
     * @public
     */
    _this.setCacheOn = function(){
        opt.useCache = true;
    };
    /**
     * Disables use of keypath cache.
     * @public
     */
    _this.setCacheOff = function(){
        opt.useCache = false;
    };

    /**
     * Sets "force" option when setting values in an object, depending on input value.
     * @public
     * @param {Any} val Value which will be interpreted as a boolean using `truthify`. "true" enables "force"; "false" disables.
     */
    _this.setForce = function(val){
        opt.force = truthify(val);
    };
    /**
     * Enables "force" option when setting values in an object.
     * @public
     */
    _this.setForceOn = function(){
        opt.force = true;
    };
    /**
     * Disables "force" option when setting values in an object.
     * @public
     */
    _this.setForceOff = function(){
        opt.force = false;
    };

    /**
     * Shortcut function to alter PathToolkit syntax to a "simple" mode that only uses
     * separators and no other operators. "Simple" mode is enabled or disabled according
     * to the first argument and the separator may be customized with the second
     * argument when enabling "simple" mode.
     * @public
     * @param {Any} val Value which will be interpreted as a boolean using `truthify`. "true" enables "simple" mode; "false" disables.
     * @param {String} sep Separator string to use in place of the default "."
     */
    _this.setSimple = function(val, sep){
        var tempCache = opt.useCache; // preserve these two options after "setDefaultOptions"
        var tempForce = opt.force;
        opt.simple = truthify(val);
        if (opt.simple){
            setSimpleOptions(sep);
            updateRegEx();
        }
        else {
            setDefaultOptions();
            updateRegEx();
            opt.useCache = tempCache;
            opt.force = tempForce;
        }
        cache = {};
    };

    /**
     * Enables "simple" mode
     * @public
     * @param {String} sep Separator string to use in place of the default "."
     * @see setSimple
     */
    _this.setSimpleOn = function(sep){
        opt.simple = true;
        setSimpleOptions(sep);
        updateRegEx();
        cache = {};
    };

    /**
     * Disables "simple" mode, restores default PathToolkit syntax
     * @public
     * @see setSimple
     * @see setDefaultOptions
     */
    _this.setSimpleOff = function(){
        var tempCache = opt.useCache; // preserve these two options after "setDefaultOptions"
        var tempForce = opt.force;
        opt.simple = false;
        setDefaultOptions();
        updateRegEx();
        opt.useCache = tempCache;
        opt.force = tempForce;
        cache = {};
    };

    /**
     * Sets default value to return if "get" resolves to undefined
     * @public
     * @param {Any} val Value which will be returned when "get" resolves to undefined
     */
    _this.setDefaultReturnVal = function(val){
        opt['defaultReturnVal'] = val;
    };

    /**
     * Modify the property separator in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for this operation.
     */
    _this.setSeparatorProperty = function(val){
        if (typeof val === $STRING && val.length === 1){
            if (val !== $WILDCARD && (!opt.separators[val] || opt.separators[val].exec === $PROPERTY) && !(opt.prefixes[val] || opt.containers[val])){
                updateOptionChar(opt.separators, $PROPERTY, val);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setSeparatorProperty - value already in use');
            }
        }
        else {
            throw new Error('setSeparatorProperty - invalid value');
        }
    };

    /**
     * Modify the collection separator in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for this operation.
     */
    _this.setSeparatorCollection = function(val){
        if (typeof val === $STRING && val.length === 1){
            if (val !== $WILDCARD && (!opt.separators[val] || opt.separators[val].exec === $COLLECTION) && !(opt.prefixes[val] || opt.containers[val])){
                updateOptionChar(opt.separators, $COLLECTION, val);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setSeparatorCollection - value already in use');
            }
        }
        else {
            throw new Error('setSeparatorCollection - invalid value');
        }
    };

    /**
     * Modify the parent prefix in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for this operation.
     */
    _this.setPrefixParent = function(val){
        if (typeof val === $STRING && val.length === 1){
            if (val !== $WILDCARD && (!opt.prefixes[val] || opt.prefixes[val].exec === $PARENT) && !(opt.separators[val] || opt.containers[val])){
                updateOptionChar(opt.prefixes, $PARENT, val);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setPrefixParent - value already in use');
            }
        }
        else {
            throw new Error('setPrefixParent - invalid value');
        }
    };

    /**
     * Modify the root prefix in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for this operation.
     */
    _this.setPrefixRoot = function(val){
        if (typeof val === $STRING && val.length === 1){
            if (val !== $WILDCARD && (!opt.prefixes[val] || opt.prefixes[val].exec === $ROOT) && !(opt.separators[val] || opt.containers[val])){
                updateOptionChar(opt.prefixes, $ROOT, val);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setPrefixRoot - value already in use');
            }
        }
        else {
            throw new Error('setPrefixRoot - invalid value');
        }
    };

    /**
     * Modify the placeholder prefix in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for this operation.
     */
    _this.setPrefixPlaceholder = function(val){
        if (typeof val === $STRING && val.length === 1){
            if (val !== $WILDCARD && (!opt.prefixes[val] || opt.prefixes[val].exec === $PLACEHOLDER) && !(opt.separators[val] || opt.containers[val])){
                updateOptionChar(opt.prefixes, $PLACEHOLDER, val);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setPrefixPlaceholder - value already in use');
            }
        }
        else {
            throw new Error('setPrefixPlaceholder - invalid value');
        }
    };

    /**
     * Modify the context prefix in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for this operation.
     */
    _this.setPrefixContext = function(val){
        if (typeof val === $STRING && val.length === 1){
            if (val !== $WILDCARD && (!opt.prefixes[val] || opt.prefixes[val].exec === $CONTEXT) && !(opt.separators[val] || opt.containers[val])){
                updateOptionChar(opt.prefixes, $CONTEXT, val);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setPrefixContext - value already in use');
            }
        }
        else {
            throw new Error('setPrefixContext - invalid value');
        }
    };

    /**
     * Modify the property container characters in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for the container opener.
     * @param {String} closer New character to use for the container closer.
     */
    _this.setContainerProperty = function(val, closer){
        if (typeof val === $STRING && val.length === 1 && typeof closer === $STRING && closer.length === 1){
            if (val !== $WILDCARD && (!opt.containers[val] || opt.containers[val].exec === $PROPERTY) && !(opt.separators[val] || opt.prefixes[val])){
                updateOptionChar(opt.containers, $PROPERTY, val, closer);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setContainerProperty - value already in use');
            }
        }
        else {
            throw new Error('setContainerProperty - invalid value');
        }
    };

    /**
     * Modify the single quote container characters in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for the container opener.
     * @param {String} closer New character to use for the container closer.
     */
    _this.setContainerSinglequote = function(val, closer){
        if (typeof val === $STRING && val.length === 1 && typeof closer === $STRING && closer.length === 1){
            if (val !== $WILDCARD && (!opt.containers[val] || opt.containers[val].exec === $SINGLEQUOTE) && !(opt.separators[val] || opt.prefixes[val])){
                updateOptionChar(opt.containers, $SINGLEQUOTE, val, closer);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setContainerSinglequote - value already in use');
            }
        }
        else {
            throw new Error('setContainerSinglequote - invalid value');
        }
    };

    /**
     * Modify the double quote container characters in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for the container opener.
     * @param {String} closer New character to use for the container closer.
     */
    _this.setContainerDoublequote = function(val, closer){
        if (typeof val === $STRING && val.length === 1 && typeof closer === $STRING && closer.length === 1){
            if (val !== $WILDCARD && (!opt.containers[val] || opt.containers[val].exec === $DOUBLEQUOTE) && !(opt.separators[val] || opt.prefixes[val])){
                updateOptionChar(opt.containers, $DOUBLEQUOTE, val, closer);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setContainerDoublequote - value already in use');
            }
        }
        else {
            throw new Error('setContainerDoublequote - invalid value');
        }
    };

    /**
     * Modify the function call container characters in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for the container opener.
     * @param {String} closer New character to use for the container closer.
     */
    _this.setContainerCall = function(val, closer){
        if (typeof val === $STRING && val.length === 1 && typeof closer === $STRING && closer.length === 1){
            if (val !== $WILDCARD && (!opt.containers[val] || opt.containers[val].exec === $CALL) && !(opt.separators[val] || opt.prefixes[val])){
                updateOptionChar(opt.containers, $CALL, val, closer);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setContainerCall - value already in use');
            }
        }
        else {
            throw new Error('setContainerCall - invalid value');
        }
    };

    /**
     * Modify the eval property container characters in the PathToolkit syntax.
     * @public
     * @param {String} val New character to use for the container opener.
     * @param {String} closer New character to use for the container closer.
     */
    _this.setContainerEvalProperty = function(val, closer){
        if (typeof val === $STRING && val.length === 1 && typeof closer === $STRING && closer.length === 1){
            if (val !== $WILDCARD && (!opt.containers[val] || opt.containers[val].exec === $EVALPROPERTY) && !(opt.separators[val] || opt.prefixes[val])){
                updateOptionChar(opt.containers, $EVALPROPERTY, val, closer);
                updateRegEx();
                cache = {};
            }
            else {
                throw new Error('setContainerEvalProperty - value already in use');
            }
        }
        else {
            throw new Error('setContainerProperty - invalid value');
        }
    };

    /**
     * Reset all PathToolkit options to their default values.
     * @public
     */
    _this.resetOptions = function(){
        setDefaultOptions();
        updateRegEx();
        cache = {};
    };

    // Initialize option set
    setDefaultOptions();
    updateRegEx();

    // Apply custom options if provided as argument to constructor
    options && _this.setOptions(options);

};

return PathToolkit;

})));

//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjpudWxsLCJzb3VyY2VzIjpbIi9ob21lL2FyanVuL1BvQy9wYXRoLXRvb2xraXQvc3JjL3BhdGgtdG9vbGtpdC5qcyJdLCJzb3VyY2VzQ29udGVudCI6WyIvKipcbiAqIEBmaWxlT3ZlcnZpZXcgUGF0aFRvb2xraXQgZXZhbHVhdGVzIHN0cmluZyBwYXRocyBhcyBwcm9wZXJ0eS9pbmRleCBzZXF1ZW5jZXMgd2l0aGluIG9iamVjdHMgYW5kIGFycmF5c1xuICogQGF1dGhvciBBYXJvbiBCcm93blxuICogQHZlcnNpb24gMS4xLjBcbiAqL1xuXG4vLyBQYXJzaW5nLCB0b2tlbmluemluZywgZXRjXG4ndXNlIHN0cmljdCc7XG5cbi8vIFNvbWUgY29uc3RhbnRzIGZvciBjb252ZW5pZW5jZVxudmFyIFVOREVGID0gKGZ1bmN0aW9uKHUpe3JldHVybiB1O30pKCk7XG5cbi8vIFN0YXRpYyBzdHJpbmdzLCBhc3NpZ25lZCB0byBhaWQgY29kZSBtaW5pZmljYXRpb25cbnZhciAkV0lMRENBUkQgICAgID0gJyonLFxuICAgICRVTkRFRklORUQgICAgPSAndW5kZWZpbmVkJyxcbiAgICAkU1RSSU5HICAgICAgID0gJ3N0cmluZycsXG4gICAgJFBBUkVOVCAgICAgICA9ICdwYXJlbnQnLFxuICAgICRST09UICAgICAgICAgPSAncm9vdCcsXG4gICAgJFBMQUNFSE9MREVSICA9ICdwbGFjZWhvbGRlcicsXG4gICAgJENPTlRFWFQgICAgICA9ICdjb250ZXh0JyxcbiAgICAkUFJPUEVSVFkgICAgID0gJ3Byb3BlcnR5JyxcbiAgICAkQ09MTEVDVElPTiAgID0gJ2NvbGxlY3Rpb24nLFxuICAgICRFQUNIICAgICAgICAgPSAnZWFjaCcsXG4gICAgJFNJTkdMRVFVT1RFICA9ICdzaW5nbGVxdW90ZScsXG4gICAgJERPVUJMRVFVT1RFICA9ICdkb3VibGVxdW90ZScsXG4gICAgJENBTEwgICAgICAgICA9ICdjYWxsJyxcbiAgICAkRVZBTFBST1BFUlRZID0gJ2V2YWxQcm9wZXJ0eSc7XG5cbi8qKlxuICogVGVzdHMgd2hldGhlciBhIHdpbGRjYXJkIHRlbXBsYXRlcyBtYXRjaGVzIGEgZ2l2ZW4gc3RyaW5nLlxuICogYGBgamF2YXNjcmlwdFxuICogdmFyIHN0ciA9ICdhYWFiYmJ4eHhjY2NkZGQnO1xuICogd2lsZENhcmRNYXRjaCgnYWFhYmJieHh4Y2NjZGRkJyk7IC8vIHRydWVcbiAqIHdpbGRDYXJkTWF0Y2goJyonLCBzdHIpOyAvLyB0cnVlXG4gKiB3aWxkQ2FyZE1hdGNoKCcqJywgJycpOyAvLyB0cnVlXG4gKiB3aWxkQ2FyZE1hdGNoKCdhKicsIHN0cik7IC8vIHRydWVcbiAqIHdpbGRDYXJkTWF0Y2goJ2FhKmRkZCcsIHN0cik7IC8vIHRydWVcbiAqIHdpbGRDYXJkTWF0Y2goJypkJywgc3RyKTsgLy8gdHJ1ZVxuICogd2lsZENhcmRNYXRjaCgnKmEnLCBzdHIpOyAvLyBmYWxzZVxuICogd2lsZENhcmRNYXRjaCgnYSp6Jywgc3RyKTsgLy8gZmFsc2VcbiAqIGBgYFxuICogQHByaXZhdGVcbiAqIEBwYXJhbSAge1N0cmluZ30gdGVtcGxhdGUgV2lsZGNhcmQgcGF0dGVyblxuICogQHBhcmFtICB7U3RyaW5nfSBzdHIgICAgICBTdHJpbmcgdG8gbWF0Y2ggYWdhaW5zdCB3aWxkY2FyZCBwYXR0ZXJuXG4gKiBAcmV0dXJuIHtCb29sZWFufSAgICAgICAgICBUcnVlIGlmIHBhdHRlcm4gbWF0Y2hlcyBzdHJpbmc7IEZhbHNlIGlmIG5vdFxuICovXG52YXIgd2lsZENhcmRNYXRjaCA9IGZ1bmN0aW9uKHRlbXBsYXRlLCBzdHIpe1xuICAgIHZhciBwb3MgPSB0ZW1wbGF0ZS5pbmRleE9mKCRXSUxEQ0FSRCksXG4gICAgICAgIHBhcnRzID0gdGVtcGxhdGUuc3BsaXQoJFdJTERDQVJELCAyKSxcbiAgICAgICAgbWF0Y2ggPSB0cnVlO1xuICAgIGlmIChwYXJ0c1swXSl7XG4gICAgICAgIC8vIElmIG5vIHdpbGRjYXJkIHByZXNlbnQsIHJldHVybiBzaW1wbGUgc3RyaW5nIGNvbXBhcmlzb25cbiAgICAgICAgaWYgKHBhcnRzWzBdID09PSB0ZW1wbGF0ZSl7XG4gICAgICAgICAgICByZXR1cm4gcGFydHNbMF0gPT09IHN0cjtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIG1hdGNoID0gbWF0Y2ggJiYgc3RyLnN1YnN0cigwLCBwYXJ0c1swXS5sZW5ndGgpID09PSBwYXJ0c1swXTtcbiAgICAgICAgfVxuICAgIH1cbiAgICBpZiAocGFydHNbMV0pe1xuICAgICAgICBtYXRjaCA9IG1hdGNoICYmIHN0ci5zdWJzdHIoLTEqcGFydHNbMV0ubGVuZ3RoKSA9PT0gcGFydHNbMV07XG4gICAgfVxuICAgIHJldHVybiBtYXRjaDtcbn07XG5cbi8qKlxuICogSW5zcGVjdCBpbnB1dCB2YWx1ZSBhbmQgZGV0ZXJtaW5lIHdoZXRoZXIgaXQgaXMgYW4gT2JqZWN0IG9yIG5vdC5cbiAqIFZhbHVlcyBvZiB1bmRlZmluZWQgYW5kIG51bGwgd2lsbCByZXR1cm4gXCJmYWxzZVwiLCBvdGhlcndpc2VcbiAqIG11c3QgYmUgb2YgdHlwZSBcIm9iamVjdFwiIG9yIFwiZnVuY3Rpb25cIi5cbiAqIEBwcml2YXRlXG4gKiBAcGFyYW0gIHtPYmplY3R9ICB2YWwgVGhpbmcgdG8gZXhhbWluZSwgbWF5IGJlIG9mIGFueSB0eXBlXG4gKiBAcmV0dXJuIHtCb29sZWFufSAgICAgVHJ1ZSBpZiB0aGluZyBpcyBvZiB0eXBlIFwib2JqZWN0XCIgb3IgXCJmdW5jdGlvblwiXG4gKi9cbnZhciBpc09iamVjdCA9IGZ1bmN0aW9uKHZhbCl7XG4gICAgaWYgKHR5cGVvZiB2YWwgPT09ICRVTkRFRklORUQgfHwgdmFsID09PSBudWxsKSB7IHJldHVybiBmYWxzZTt9XG4gICAgcmV0dXJuICggKHR5cGVvZiB2YWwgPT09ICdmdW5jdGlvbicpIHx8ICh0eXBlb2YgdmFsID09PSAnb2JqZWN0JykgKTtcbn07XG5cbi8qKlxuICogSW5zcGVjdCBpbnB1dCB2YWx1ZSBhbmQgZGV0ZXJtaW5lIHdoZXRoZXIgaXQgaXMgYW4gSW50ZWdlciBvciBub3QuXG4gKiBWYWx1ZXMgb2YgdW5kZWZpbmVkIGFuZCBudWxsIHdpbGwgcmV0dXJuIFwiZmFsc2VcIi5cbiAqIEBwcml2YXRlXG4gKiBAcGFyYW0gIHtTdHJpbmd9ICB2YWwgU3RyaW5nIHRvIGV4YW1pbmVcbiAqIEByZXR1cm4ge0Jvb2xlYW59ICAgICBUcnVlIGlmIHRoaW5nIGNvbnNpc3RzIG9mIGF0IGxlYXN0IG9uZSBkaWdpdCBhbmQgb25seSBvZiBkaWdpdHMgKG5vIC4gb3IgLClcbiAqL1xudmFyIGRpZ2l0c1JlZ2V4ID0gL15cXGQrJC87XG52YXIgaXNEaWdpdHMgPSBmdW5jdGlvbih2YWwpe1xuICAgIHJldHVybiBkaWdpdHNSZWdleC50ZXN0KHZhbCk7XG59O1xuXG4vKipcbiAqIENvbnZlcnQgdmFyaW91cyB2YWx1ZXMgdG8gdHJ1ZSBib29sZWFuIGB0cnVlYCBvciBgZmFsc2VgLlxuICogRm9yIG5vbi1zdHJpbmcgdmFsdWVzLCB0aGUgbmF0aXZlIGphdmFzY3JpcHQgaWRlYSBvZiBcInRydWVcIiB3aWxsIGFwcGx5LlxuICogRm9yIHN0cmluZyB2YWx1ZXMsIHRoZSB3b3JkcyBcInRydWVcIiwgXCJ5ZXNcIiwgYW5kIFwib25cIiB3aWxsIGFsbCByZXR1cm4gYHRydWVgLlxuICogQWxsIG90aGVyIHN0cmluZ3MgcmV0dXJuIGBmYWxzZWAuIFRoZSBzdHJpbmcgbWF0Y2ggaXMgbm9uLWNhc2Utc2Vuc2l0aXZlLlxuICogQHByaXZhdGVcbiAqL1xudmFyIHRydXRoaWZ5ID0gZnVuY3Rpb24odmFsKXtcbiAgICB2YXIgdjtcbiAgICBpZiAodHlwZW9mIHZhbCAhPT0gJFNUUklORyl7XG4gICAgICAgIHJldHVybiB2YWwgJiYgdHJ1ZTsgLy8gVXNlIG5hdGl2ZSBqYXZhc2NyaXB0IG5vdGlvbiBvZiBcInRydXRoeVwiXG4gICAgfVxuICAgIHYgPSB2YWwudG9VcHBlckNhc2UoKTtcbiAgICBpZiAodiA9PT0gJ1RSVUUnIHx8IHYgPT09ICdZRVMnIHx8IHYgPT09ICdPTicpe1xuICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICB9XG4gICAgcmV0dXJuIGZhbHNlO1xufTtcblxuLyoqXG4gKiBVc2luZyBwcm92aWRlZCBxdW90ZSBjaGFyYWN0ZXIgYXMgcHJlZml4IGFuZCBzdWZmaXgsIGVzY2FwZSBhbnkgaW5zdGFuY2VzXG4gKiBvZiB0aGUgcXVvdGUgY2hhcmFjdGVyIHdpdGhpbiB0aGUgc3RyaW5nIGFuZCByZXR1cm4gcXVvdGUrc3RyaW5nK3F1b3RlLlxuICogVGhlIGNoYXJhY3RlciBkZWZpbmVkIGFzIFwic2luZ2xlcXVvdGVcIiBtYXkgYmUgYWx0ZXJlZCBieSBjdXN0b20gb3B0aW9ucyxcbiAqIHNvIGEgZ2VuZXJhbC1wdXJwb3NlIGZ1bmN0aW9uIGlzIG5lZWRlZCB0byBxdW90ZSBwYXRoIHNlZ21lbnRzIGNvcnJlY3RseS5cbiAqIEBwcml2YXRlXG4gKiBAcGFyYW0gIHtTdHJpbmd9IHEgICBTaW5nbGUtY2hhcmFjdGVyIHN0cmluZyB0byB1c2UgYXMgcXVvdGUgY2hhcmFjdGVyXG4gKiBAcGFyYW0gIHtTdHJpbmd9IHN0ciBTdHJpbmcgdG8gYmUgcXVvdGVkLlxuICogQHJldHVybiB7U3RyaW5nfSAgICAgT3JpZ2luYWwgc3RyaW5nLCBzdXJyb3VuZGVkIGJ5IHRoZSBxdW90ZSBjaGFyYWN0ZXIsIHBvc3NpYmx5IG1vZGlmaWVkIGludGVybmFsbHkgaWYgdGhlIHF1b3RlIGNoYXJhY3RlciBleGlzdHMgd2l0aGluIHRoZSBzdHJpbmcuXG4gKi9cbnZhciBxdW90ZVN0cmluZyA9IGZ1bmN0aW9uKHEsIHN0cil7XG4gICAgdmFyIHFSZWdFeCA9IG5ldyBSZWdFeHAocSwgJ2cnKTtcbiAgICByZXR1cm4gcSArIHN0ci5yZXBsYWNlKHFSZWdFeCwgJ1xcXFwnICsgcSkgKyBxO1xufTtcblxuLyoqXG4gKiBQYXRoVG9vbGtpdCBiYXNlIG9iamVjdC4gSW5jbHVkZXMgYWxsIGluc3RhbmNlLXNwZWNpZmljIGRhdGEgKG9wdGlvbnMsIGNhY2hlKVxuICogYXMgbG9jYWwgdmFyaWFibGVzLiBNYXkgYmUgcGFzc2VkIGFuIG9wdGlvbnMgaGFzaCB0byBwcmUtY29uZmlndXJlIHRoZVxuICogaW5zdGFuY2UgcHJpb3IgdG8gdXNlLlxuICogQGNvbnN0cnVjdG9yXG4gKiBAcHJvcGVydHkge09iamVjdH0gb3B0aW9ucyBPcHRpb25hbC4gQ29sbGVjdGlvbiBvZiBjb25maWd1cmF0aW9uIHNldHRpbmdzIGZvciB0aGlzIGluc3RhbmNlIG9mIFBhdGhUb29sa2l0LiBTZWUgYHNldE9wdGlvbnNgIGZ1bmN0aW9uIGJlbG93IGZvciBkZXRhaWxlZCBkb2N1bWVudGF0aW9uLlxuICovXG52YXIgUGF0aFRvb2xraXQgPSBmdW5jdGlvbihvcHRpb25zKXtcbiAgICB2YXIgX3RoaXMgPSB0aGlzLFxuICAgICAgICBjYWNoZSA9IHt9LFxuICAgICAgICBvcHQgPSB7fSxcbiAgICAgICAgcHJlZml4TGlzdCwgc2VwYXJhdG9yTGlzdCwgY29udGFpbmVyTGlzdCwgY29udGFpbmVyQ2xvc2VMaXN0LFxuICAgICAgICBwcm9wZXJ0eVNlcGFyYXRvcixcbiAgICAgICAgc2luZ2xlcXVvdGUsIGRvdWJsZXF1b3RlLFxuICAgICAgICBzaW1wbGVQYXRoQ2hhcnMsIHNpbXBsZVBhdGhSZWdFeCxcbiAgICAgICAgYWxsU3BlY2lhbHMsIGFsbFNwZWNpYWxzUmVnRXgsXG4gICAgICAgIGVzY2FwZWROb25TcGVjaWFsc1JlZ0V4LFxuICAgICAgICBlc2NhcGVkUXVvdGVzLFxuICAgICAgICB3aWxkY2FyZFJlZ0V4O1xuXG4gICAgLyoqXG4gICAgICogU2V2ZXJhbCByZWd1bGFyIGV4cHJlc3Npb25zIGFyZSBwcmUtY29tcGlsZWQgZm9yIHVzZSBpbiBwYXRoIGludGVycHJldGF0aW9uLlxuICAgICAqIFRoZXNlIGV4cHJlc3Npb25zIGFyZSBidWlsdCBmcm9tIHRoZSBjdXJyZW50IHN5bnRheCBjb25maWd1cmF0aW9uLCBzbyB0aGV5XG4gICAgICogbXVzdCBiZSByZS1idWlsdCBldmVyeSB0aW1lIHRoZSBzeW50YXggY2hhbmdlcy5cbiAgICAgKiBAcHJpdmF0ZVxuICAgICAqL1xuICAgIHZhciB1cGRhdGVSZWdFeCA9IGZ1bmN0aW9uKCl7XG4gICAgICAgIC8vIExpc3RzIG9mIHNwZWNpYWwgY2hhcmFjdGVycyBmb3IgdXNlIGluIHJlZ3VsYXIgZXhwcmVzc2lvbnNcbiAgICAgICAgcHJlZml4TGlzdCA9IE9iamVjdC5rZXlzKG9wdC5wcmVmaXhlcyk7XG4gICAgICAgIHNlcGFyYXRvckxpc3QgPSBPYmplY3Qua2V5cyhvcHQuc2VwYXJhdG9ycyk7XG4gICAgICAgIGNvbnRhaW5lckxpc3QgPSBPYmplY3Qua2V5cyhvcHQuY29udGFpbmVycyk7XG4gICAgICAgIGNvbnRhaW5lckNsb3NlTGlzdCA9IGNvbnRhaW5lckxpc3QubWFwKGZ1bmN0aW9uKGtleSl7IHJldHVybiBvcHQuY29udGFpbmVyc1trZXldLmNsb3NlcjsgfSk7XG5cbiAgICAgICAgcHJvcGVydHlTZXBhcmF0b3IgPSAnJztcbiAgICAgICAgT2JqZWN0LmtleXMob3B0LnNlcGFyYXRvcnMpLmZvckVhY2goZnVuY3Rpb24oc2VwKXsgaWYgKG9wdC5zZXBhcmF0b3JzW3NlcF0uZXhlYyA9PT0gJFBST1BFUlRZKXsgcHJvcGVydHlTZXBhcmF0b3IgPSBzZXA7IH0gfSk7XG4gICAgICAgIHNpbmdsZXF1b3RlID0gJyc7XG4gICAgICAgIGRvdWJsZXF1b3RlID0gJyc7XG4gICAgICAgIE9iamVjdC5rZXlzKG9wdC5jb250YWluZXJzKS5mb3JFYWNoKGZ1bmN0aW9uKHNlcCl7XG4gICAgICAgICAgICBpZiAob3B0LmNvbnRhaW5lcnNbc2VwXS5leGVjID09PSAkU0lOR0xFUVVPVEUpeyBzaW5nbGVxdW90ZSA9IHNlcDt9XG4gICAgICAgICAgICBpZiAob3B0LmNvbnRhaW5lcnNbc2VwXS5leGVjID09PSAkRE9VQkxFUVVPVEUpeyBkb3VibGVxdW90ZSA9IHNlcDt9XG4gICAgICAgIH0pO1xuXG4gICAgICAgIC8vIEZpbmQgYWxsIHNwZWNpYWwgY2hhcmFjdGVycyBleGNlcHQgcHJvcGVydHkgc2VwYXJhdG9yICguIGJ5IGRlZmF1bHQpXG4gICAgICAgIHNpbXBsZVBhdGhDaGFycyA9ICdbXFxcXFxcXFwnICsgWyRXSUxEQ0FSRF0uY29uY2F0KHByZWZpeExpc3QpLmNvbmNhdChzZXBhcmF0b3JMaXN0KS5jb25jYXQoY29udGFpbmVyTGlzdCkuam9pbignXFxcXCcpLnJlcGxhY2UoJ1xcXFwnK3Byb3BlcnR5U2VwYXJhdG9yLCAnJykgKyAnXSc7XG4gICAgICAgIHNpbXBsZVBhdGhSZWdFeCA9IG5ldyBSZWdFeHAoc2ltcGxlUGF0aENoYXJzKTtcblxuICAgICAgICAvLyBGaW5kIGFsbCBzcGVjaWFsIGNoYXJhY3RlcnMsIGluY2x1ZGluZyBiYWNrc2xhc2hcbiAgICAgICAgYWxsU3BlY2lhbHMgPSAnW1xcXFxcXFxcXFxcXCcgKyBbJFdJTERDQVJEXS5jb25jYXQocHJlZml4TGlzdCkuY29uY2F0KHNlcGFyYXRvckxpc3QpLmNvbmNhdChjb250YWluZXJMaXN0KS5jb25jYXQoY29udGFpbmVyQ2xvc2VMaXN0KS5qb2luKCdcXFxcJykgKyAnXSc7XG4gICAgICAgIGFsbFNwZWNpYWxzUmVnRXggPSBuZXcgUmVnRXhwKGFsbFNwZWNpYWxzLCAnZycpO1xuXG4gICAgICAgIC8vIEZpbmQgYWxsIGVzY2FwZWQgc3BlY2lhbCBjaGFyYWN0ZXJzXG4gICAgICAgIC8vIGVzY2FwZWRTcGVjaWFsc1JlZ0V4ID0gbmV3IFJlZ0V4cCgnXFxcXCcrYWxsU3BlY2lhbHMsICdnJyk7XG4gICAgICAgIC8vIEZpbmQgYWxsIGVzY2FwZWQgbm9uLXNwZWNpYWwgY2hhcmFjdGVycywgaS5lLiB1bm5lY2Vzc2FyeSBlc2NhcGVzXG4gICAgICAgIGVzY2FwZWROb25TcGVjaWFsc1JlZ0V4ID0gbmV3IFJlZ0V4cCgnXFxcXCcrYWxsU3BlY2lhbHMucmVwbGFjZSgvXlxcWy8sJ1teJykpO1xuICAgICAgICBpZiAoc2luZ2xlcXVvdGUgfHwgZG91YmxlcXVvdGUpe1xuICAgICAgICAgICAgZXNjYXBlZFF1b3RlcyA9IG5ldyBSZWdFeHAoJ1xcXFxbJytzaW5nbGVxdW90ZStkb3VibGVxdW90ZSsnXScsICdnJyk7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICBlc2NhcGVkUXVvdGVzID0gJyc7XG4gICAgICAgIH1cblxuICAgICAgICAvLyBGaW5kIHdpbGRjYXJkIGNoYXJhY3RlclxuICAgICAgICB3aWxkY2FyZFJlZ0V4ID0gbmV3IFJlZ0V4cCgnXFxcXCcrJFdJTERDQVJEKTtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogU2V0cyBhbGwgdGhlIGRlZmF1bHQgb3B0aW9ucyBmb3IgaW50ZXJwcmV0ZXIgYmVoYXZpb3IgYW5kIHN5bnRheC5cbiAgICAgKiBAcHJpdmF0ZVxuICAgICAqL1xuICAgIHZhciBzZXREZWZhdWx0T3B0aW9ucyA9IGZ1bmN0aW9uKCl7XG4gICAgICAgIG9wdCA9IG9wdCB8fCB7fTtcbiAgICAgICAgLy8gRGVmYXVsdCBzZXR0aW5nc1xuICAgICAgICBvcHQudXNlQ2FjaGUgPSB0cnVlOyAgLy8gY2FjaGUgdG9rZW5pemVkIHBhdGhzIGZvciByZXBlYXRlZCB1c2VcbiAgICAgICAgb3B0LnNpbXBsZSA9IGZhbHNlOyAgIC8vIG9ubHkgc3VwcG9ydCBkb3Qtc2VwYXJhdGVkIHBhdGhzLCBubyBvdGhlciBzcGVjaWFsIGNoYXJhY3RlcnNcbiAgICAgICAgb3B0LmZvcmNlID0gZmFsc2U7ICAgIC8vIGNyZWF0ZSBpbnRlcm1lZGlhdGUgcHJvcGVydGllcyBkdXJpbmcgYHNldGAgb3BlcmF0aW9uXG4gICAgICAgIG9wdFsnZGVmYXVsdFJldHVyblZhbCddID0gVU5ERUY7ICAgLy8gcmV0dXJuIHVuZGVmaW5lZCBieSBkZWZhdWx0IHdoZW4gcGF0aCByZXNvbHV0aW9uIGZhaWxzXG5cbiAgICAgICAgLy8gRGVmYXVsdCBwcmVmaXggc3BlY2lhbCBjaGFyYWN0ZXJzXG4gICAgICAgIG9wdC5wcmVmaXhlcyA9IHtcbiAgICAgICAgICAgICdeJzoge1xuICAgICAgICAgICAgICAgICdleGVjJzogJFBBUkVOVFxuICAgICAgICAgICAgfSxcbiAgICAgICAgICAgICd+Jzoge1xuICAgICAgICAgICAgICAgICdleGVjJzogJFJPT1RcbiAgICAgICAgICAgIH0sXG4gICAgICAgICAgICAnJSc6IHtcbiAgICAgICAgICAgICAgICAnZXhlYyc6ICRQTEFDRUhPTERFUlxuICAgICAgICAgICAgfSxcbiAgICAgICAgICAgICdAJzoge1xuICAgICAgICAgICAgICAgICdleGVjJzogJENPTlRFWFRcbiAgICAgICAgICAgIH1cbiAgICAgICAgfTtcbiAgICAgICAgLy8gRGVmYXVsdCBzZXBhcmF0b3Igc3BlY2lhbCBjaGFyYWN0ZXJzXG4gICAgICAgIG9wdC5zZXBhcmF0b3JzID0ge1xuICAgICAgICAgICAgJy4nOiB7XG4gICAgICAgICAgICAgICAgJ2V4ZWMnOiAkUFJPUEVSVFlcbiAgICAgICAgICAgICAgICB9LFxuICAgICAgICAgICAgJywnOiB7XG4gICAgICAgICAgICAgICAgJ2V4ZWMnOiAkQ09MTEVDVElPTlxuICAgICAgICAgICAgICAgIH0sXG4gICAgICAgICAgICAnPCc6IHtcbiAgICAgICAgICAgICAgICAnZXhlYyc6ICRFQUNIXG4gICAgICAgICAgICB9XG4gICAgICAgIH07XG4gICAgICAgIC8vIERlZmF1bHQgY29udGFpbmVyIHNwZWNpYWwgY2hhcmFjdGVyc1xuICAgICAgICBvcHQuY29udGFpbmVycyA9IHtcbiAgICAgICAgICAgICdbJzoge1xuICAgICAgICAgICAgICAgICdjbG9zZXInOiAnXScsXG4gICAgICAgICAgICAgICAgJ2V4ZWMnOiAkUFJPUEVSVFlcbiAgICAgICAgICAgICAgICB9LFxuICAgICAgICAgICAgJ1xcJyc6IHtcbiAgICAgICAgICAgICAgICAnY2xvc2VyJzogJ1xcJycsXG4gICAgICAgICAgICAgICAgJ2V4ZWMnOiAkU0lOR0xFUVVPVEVcbiAgICAgICAgICAgICAgICB9LFxuICAgICAgICAgICAgJ1wiJzoge1xuICAgICAgICAgICAgICAgICdjbG9zZXInOiAnXCInLFxuICAgICAgICAgICAgICAgICdleGVjJzogJERPVUJMRVFVT1RFXG4gICAgICAgICAgICAgICAgfSxcbiAgICAgICAgICAgICcoJzoge1xuICAgICAgICAgICAgICAgICdjbG9zZXInOiAnKScsXG4gICAgICAgICAgICAgICAgJ2V4ZWMnOiAkQ0FMTFxuICAgICAgICAgICAgICAgIH0sXG4gICAgICAgICAgICAneyc6IHtcbiAgICAgICAgICAgICAgICAnY2xvc2VyJzogJ30nLFxuICAgICAgICAgICAgICAgICdleGVjJzogJEVWQUxQUk9QRVJUWVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgfTtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogVGVzdCBzdHJpbmcgdG8gc2VlIGlmIGl0IGlzIHN1cnJvdW5kZWQgYnkgc2luZ2xlLSBvciBkb3VibGUtcXVvdGUsIHVzaW5nIHRoZVxuICAgICAqIGN1cnJlbnQgY29uZmlndXJhdGlvbiBkZWZpbml0aW9uIGZvciB0aG9zZSBjaGFyYWN0ZXJzLiBJZiBubyBxdW90ZSBjb250YWluZXJcbiAgICAgKiBpcyBkZWZpbmVkLCB0aGlzIGZ1bmN0aW9uIHdpbGwgcmV0dXJuIGZhbHNlIHNpbmNlIGl0J3Mgbm90IHBvc3NpYmxlIHRvIHF1b3RlXG4gICAgICogdGhlIHN0cmluZyBpZiB0aGVyZSBhcmUgbm8gcXVvdGVzIGluIHRoZSBzeW50YXguIEFsc28gaWdub3JlcyBlc2NhcGVkIHF1b3RlXG4gICAgICogY2hhcmFjdGVycy5cbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gc3RyIFRoZSBzdHJpbmcgdG8gdGVzdCBmb3IgZW5jbG9zaW5nIHF1b3Rlc1xuICAgICAqIEByZXR1cm4ge0Jvb2xlYW59IHRydWUgPSBzdHJpbmcgaXMgZW5jbG9zZWQgaW4gcXVvdGVzOyBmYWxzZSA9IG5vdCBxdW90ZWRcbiAgICAgKi9cbiAgICB2YXIgaXNRdW90ZWQgPSBmdW5jdGlvbihzdHIpe1xuICAgICAgICB2YXIgY2xlYW5TdHIgPSBzdHIucmVwbGFjZShlc2NhcGVkUXVvdGVzLCAnJyk7XG4gICAgICAgIHZhciBzdHJMZW4gPSBjbGVhblN0ci5sZW5ndGg7XG4gICAgICAgIGlmIChzdHJMZW4gPCAyKXsgcmV0dXJuIGZhbHNlOyB9XG4gICAgICAgIHJldHVybiAgKGNsZWFuU3RyWzBdID09PSBjbGVhblN0cltzdHJMZW4gLSAxXSkgJiZcbiAgICAgICAgICAgICAgICAoY2xlYW5TdHJbMF0gPT09IHNpbmdsZXF1b3RlIHx8IGNsZWFuU3RyWzBdID09PSBkb3VibGVxdW90ZSk7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIFJlbW92ZSBlbmNsb3NpbmcgcXVvdGVzIGZyb20gYSBzdHJpbmcuIFRoZSBpc1F1b3RlZCBmdW5jdGlvbiB3aWxsIGRldGVybWluZVxuICAgICAqIGlmIGFueSBjaGFuZ2UgaXMgbmVlZGVkLiBJZiB0aGUgc3RyaW5nIGlzIHF1b3RlZCwgd2Uga25vdyB0aGUgZmlyc3QgYW5kIGxhc3RcbiAgICAgKiBjaGFyYWN0ZXJzIGFyZSBxdW90ZSBtYXJrcywgc28gc2ltcGx5IGRvIGEgc3RyaW5nIHNsaWNlLiBJZiB0aGUgaW5wdXQgdmFsdWUgaXNcbiAgICAgKiBub3QgcXVvdGVkLCByZXR1cm4gdGhlIGlucHV0IHZhbHVlIHVuY2hhbmdlZC4gQmVjYXVzZSBpc1F1b3RlZCBpcyB1c2VkLCBpZlxuICAgICAqIG5vIHF1b3RlIG1hcmtzIGFyZSBkZWZpbmVkIGluIHRoZSBzeW50YXgsIHRoaXMgZnVuY3Rpb24gd2lsbCByZXR1cm4gdGhlIGlucHV0IHZhbHVlLlxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBzdHIgVGhlIHN0cmluZyB0byB1bi1xdW90ZVxuICAgICAqIEByZXR1cm4ge1N0cmluZ30gVGhlIGlucHV0IHN0cmluZyB3aXRob3V0IGFueSBlbmNsb3NpbmcgcXVvdGUgbWFya3MuXG4gICAgICovXG4gICAgdmFyIHN0cmlwUXVvdGVzID0gZnVuY3Rpb24oc3RyKXtcbiAgICAgICAgaWYgKGlzUXVvdGVkKHN0cikpe1xuICAgICAgICAgICAgcmV0dXJuIHN0ci5zbGljZSgxLCAtMSk7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHN0cjtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogU2NhbiBpbnB1dCBzdHJpbmcgZnJvbSBsZWZ0IHRvIHJpZ2h0LCBvbmUgY2hhcmFjdGVyIGF0IGEgdGltZS4gSWYgYSBzcGVjaWFsIGNoYXJhY3RlclxuICAgICAqIGlzIGZvdW5kIChvbmUgb2YgXCJzZXBhcmF0b3JzXCIsIFwiY29udGFpbmVyc1wiLCBvciBcInByZWZpeGVzXCIpLCBlaXRoZXIgc3RvcmUgdGhlIGFjY3VtdWxhdGVkXG4gICAgICogd29yZCBhcyBhIHRva2VuIG9yIGVsc2UgYmVnaW4gd2F0Y2hpbmcgaW5wdXQgZm9yIGVuZCBvZiB0b2tlbiAoZmluZGluZyBhIGNsb3NpbmcgY2hhcmFjdGVyXG4gICAgICogZm9yIGEgY29udGFpbmVyIG9yIHRoZSBlbmQgb2YgYSBjb2xsZWN0aW9uKS4gSWYgYSBjb250YWluZXIgaXMgZm91bmQsIGNhcHR1cmUgdGhlIHN1YnN0cmluZ1xuICAgICAqIHdpdGhpbiB0aGUgY29udGFpbmVyIGFuZCByZWN1cnNpdmVseSBjYWxsIGB0b2tlbml6ZWAgb24gdGhhdCBzdWJzdHJpbmcuIEZpbmFsIG91dHB1dCB3aWxsXG4gICAgICogYmUgYW4gYXJyYXkgb2YgdG9rZW5zLiBBIGNvbXBsZXggdG9rZW4gKG5vdCBhIHNpbXBsZSBwcm9wZXJ0eSBvciBpbmRleCkgd2lsbCBiZSByZXByZXNlbnRlZFxuICAgICAqIGFzIGFuIG9iamVjdCBjYXJyeWluZyBtZXRhZGF0YSBmb3IgcHJvY2Vzc2luZy5cbiAgICAgKiBAcHJpdmF0ZVxuICAgICAqIEBwYXJhbSAge1N0cmluZ30gc3RyIFBhdGggc3RyaW5nXG4gICAgICogQHJldHVybiB7QXJyYXl9ICAgICBBcnJheSBvZiB0b2tlbnMgZm91bmQgaW4gdGhlIGlucHV0IHBhdGhcbiAgICAgKi9cbiAgICB2YXIgdG9rZW5pemUgPSBmdW5jdGlvbiAoc3RyKXtcbiAgICAgICAgdmFyIHBhdGggPSAnJyxcbiAgICAgICAgICAgIHNpbXBsZVBhdGggPSB0cnVlLCAvLyBwYXRoIGlzIGFzc3VtZWQgXCJzaW1wbGVcIiB1bnRpbCBwcm92ZW4gb3RoZXJ3aXNlXG4gICAgICAgICAgICB0b2tlbnMgPSBbXSxcbiAgICAgICAgICAgIHJlY3VyID0gW10sXG4gICAgICAgICAgICBtb2RzID0ge30sXG4gICAgICAgICAgICBwYXRoTGVuZ3RoID0gMCxcbiAgICAgICAgICAgIHdvcmQgPSAnJyxcbiAgICAgICAgICAgIGhhc1dpbGRjYXJkID0gZmFsc2UsXG4gICAgICAgICAgICBkb0VhY2ggPSBmYWxzZSwgLy8gbXVzdCByZW1lbWJlciB0aGUgXCJlYWNoXCIgb3BlcmF0b3IgaW50byB0aGUgZm9sbG93aW5nIHRva2VuXG4gICAgICAgICAgICBzdWJwYXRoID0gJycsXG4gICAgICAgICAgICBpID0gMCxcbiAgICAgICAgICAgIG9wZW5lciA9ICcnLFxuICAgICAgICAgICAgY2xvc2VyID0gJycsXG4gICAgICAgICAgICBzZXBhcmF0b3IgPSAnJyxcbiAgICAgICAgICAgIGNvbGxlY3Rpb24gPSBbXSxcbiAgICAgICAgICAgIGRlcHRoID0gMCxcbiAgICAgICAgICAgIGVzY2FwZWQgPSAwO1xuXG4gICAgICAgIGlmIChvcHQudXNlQ2FjaGUgJiYgY2FjaGVbc3RyXSAhPT0gVU5ERUYpeyByZXR1cm4gY2FjaGVbc3RyXTsgfVxuXG4gICAgICAgIC8vIFN0cmlwIG91dCBhbnkgdW5uZWNlc3NhcnkgZXNjYXBpbmcgdG8gc2ltcGxpZnkgcHJvY2Vzc2luZyBiZWxvd1xuICAgICAgICBwYXRoID0gc3RyLnJlcGxhY2UoZXNjYXBlZE5vblNwZWNpYWxzUmVnRXgsICckJicuc3Vic3RyKDEpKTtcbiAgICAgICAgcGF0aExlbmd0aCA9IHBhdGgubGVuZ3RoO1xuXG4gICAgICAgIGlmICh0eXBlb2Ygc3RyID09PSAkU1RSSU5HICYmICFzaW1wbGVQYXRoUmVnRXgudGVzdChzdHIpKXtcbiAgICAgICAgICAgIHRva2VucyA9IHBhdGguc3BsaXQocHJvcGVydHlTZXBhcmF0b3IpO1xuICAgICAgICAgICAgb3B0LnVzZUNhY2hlICYmIChjYWNoZVtzdHJdID0ge3Q6IHRva2Vucywgc2ltcGxlOiBzaW1wbGVQYXRofSk7XG4gICAgICAgICAgICByZXR1cm4ge3Q6IHRva2Vucywgc2ltcGxlOiBzaW1wbGVQYXRofTtcbiAgICAgICAgfVxuXG4gICAgICAgIGZvciAoaSA9IDA7IGkgPCBwYXRoTGVuZ3RoOyBpKyspe1xuICAgICAgICAgICAgLy8gU2tpcCBlc2NhcGUgY2hhcmFjdGVyIChgXFxgKSBhbmQgc2V0IFwiZXNjYXBlZFwiIHRvIHRoZSBpbmRleCB2YWx1ZVxuICAgICAgICAgICAgLy8gb2YgdGhlIGNoYXJhY3RlciB0byBiZSB0cmVhdGVkIGFzIGEgbGl0ZXJhbFxuICAgICAgICAgICAgaWYgKCFlc2NhcGVkICYmIHBhdGhbaV0gPT09ICdcXFxcJyl7XG4gICAgICAgICAgICAgICAgLy8gTmV4dCBjaGFyYWN0ZXIgaXMgdGhlIGVzY2FwZWQgY2hhcmFjdGVyXG4gICAgICAgICAgICAgICAgZXNjYXBlZCA9IGkrMTtcbiAgICAgICAgICAgICAgICBpKys7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICAvLyBJZiBhIHdpbGRjYXJkIGNoYXJhY3RlciBpcyBmb3VuZCwgbWFyayB0aGlzIHRva2VuIGFzIGhhdmluZyBhIHdpbGRjYXJkXG4gICAgICAgICAgICBpZiAocGF0aFtpXSA9PT0gJFdJTERDQVJEKSB7XG4gICAgICAgICAgICAgICAgaGFzV2lsZGNhcmQgPSB0cnVlO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgLy8gSWYgd2UgaGF2ZSBhbHJlYWR5IHByb2Nlc3NlZCBhIGNvbnRhaW5lciBvcGVuZXIsIHRyZWF0IHRoaXMgc3VicGF0aCBzcGVjaWFsbHlcbiAgICAgICAgICAgIGlmIChkZXB0aCA+IDApe1xuICAgICAgICAgICAgICAgIC8vIElzIHRoaXMgY2hhcmFjdGVyIGFub3RoZXIgb3BlbmVyIGZyb20gdGhlIHNhbWUgY29udGFpbmVyPyBJZiBzbywgYWRkIHRvXG4gICAgICAgICAgICAgICAgLy8gdGhlIGRlcHRoIGxldmVsIHNvIHdlIGNhbiBtYXRjaCB0aGUgY2xvc2VycyBjb3JyZWN0bHkuIChFeGNlcHQgZm9yIHF1b3Rlc1xuICAgICAgICAgICAgICAgIC8vIHdoaWNoIGNhbm5vdCBiZSBuZXN0ZWQpXG4gICAgICAgICAgICAgICAgLy8gSXMgdGhpcyBjaGFyYWN0ZXIgdGhlIGNsb3Nlcj8gSWYgc28sIGJhY2sgb3V0IG9uZSBsZXZlbCBvZiBkZXB0aC5cbiAgICAgICAgICAgICAgICAvLyBCZSBjYXJlZnVsOiBxdW90ZSBjb250YWluZXIgdXNlcyBzYW1lIGNoYXJhY3RlciBmb3Igb3BlbmVyIGFuZCBjbG9zZXIuXG4gICAgICAgICAgICAgICAgIWVzY2FwZWQgJiYgcGF0aFtpXSA9PT0gb3BlbmVyICYmIG9wZW5lciAhPT0gY2xvc2VyLmNsb3NlciAmJiBkZXB0aCsrO1xuICAgICAgICAgICAgICAgICFlc2NhcGVkICYmIHBhdGhbaV0gPT09IGNsb3Nlci5jbG9zZXIgJiYgZGVwdGgtLTtcblxuICAgICAgICAgICAgICAgIC8vIFdoaWxlIHN0aWxsIGluc2lkZSB0aGUgY29udGFpbmVyLCBqdXN0IGFkZCB0byB0aGUgc3VicGF0aFxuICAgICAgICAgICAgICAgIGlmIChkZXB0aCA+IDApe1xuICAgICAgICAgICAgICAgICAgICBzdWJwYXRoICs9IHBhdGhbaV07XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIC8vIFdoZW4gd2UgY2xvc2Ugb2ZmIHRoZSBjb250YWluZXIsIHRpbWUgdG8gcHJvY2VzcyB0aGUgc3VicGF0aCBhbmQgYWRkIHJlc3VsdHMgdG8gb3VyIHRva2Vuc1xuICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAvLyBIYW5kbGUgc3VicGF0aCBcIltiYXJdXCIgaW4gZm9vLltiYXJdLFtiYXpdIC0gd2UgbXVzdCBwcm9jZXNzIHN1YnBhdGggYW5kIGNyZWF0ZSBhIG5ldyBjb2xsZWN0aW9uXG4gICAgICAgICAgICAgICAgICAgIGlmIChpKzEgPCBwYXRoTGVuZ3RoICYmIG9wdC5zZXBhcmF0b3JzW3BhdGhbaSsxXV0gJiYgb3B0LnNlcGFyYXRvcnNbcGF0aFtpKzFdXS5leGVjID09PSAkQ09MTEVDVElPTil7XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoc3VicGF0aC5sZW5ndGggJiYgY2xvc2VyLmV4ZWMgPT09ICRQUk9QRVJUWSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIgPSBzdHJpcFF1b3RlcyhzdWJwYXRoKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKGNsb3Nlci5leGVjID09PSAkU0lOR0xFUVVPVEUgfHwgY2xvc2VyLmV4ZWMgPT09ICRET1VCTEVRVU9URSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKG1vZHMuaGFzKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIgPSB7J3cnOiBzdWJwYXRoLCAnbW9kcyc6IG1vZHMsICdkb0VhY2gnOiBkb0VhY2h9O1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyB0b2tlbnMucHVzaCh3b3JkKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbW9kcyA9IHt9O1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IGZhbHNlO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIgPSBzdWJwYXRoO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IHRydWU7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIgPSB0b2tlbml6ZShzdWJwYXRoKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAocmVjdXIgPT09IFVOREVGKXsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyLmV4ZWMgPSBjbG9zZXIuZXhlYztcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ci5kb0VhY2ggPSBkb0VhY2g7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAvLyBjb2xsZWN0aW9uLnB1c2goY2xvc2VyLmV4ZWMgPT09ICRQUk9QRVJUWSA/IHJlY3VyLnRbMF0gOiByZWN1cik7XG4gICAgICAgICAgICAgICAgICAgICAgICBjb2xsZWN0aW9uLnB1c2gocmVjdXIpO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIC8vIEhhbmRsZSBzdWJwYXRoIFwiW2Jhel1cIiBpbiBmb28uW2Jhcl0sW2Jhel0gLSB3ZSBtdXN0IHByb2Nlc3Mgc3VicGF0aCBhbmQgYWRkIHRvIGNvbGxlY3Rpb25cbiAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAoY29sbGVjdGlvblswXSl7XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoc3VicGF0aC5sZW5ndGggJiYgY2xvc2VyLmV4ZWMgPT09ICRQUk9QRVJUWSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIgPSBzdHJpcFF1b3RlcyhzdWJwYXRoKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKGNsb3Nlci5leGVjID09PSAkU0lOR0xFUVVPVEUgfHwgY2xvc2VyLmV4ZWMgPT09ICRET1VCTEVRVU9URSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKG1vZHMuaGFzKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIgPSB7J3cnOiBzdWJwYXRoLCAnbW9kcyc6IG1vZHMsICdkb0VhY2gnOiBkb0VhY2h9O1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyB0b2tlbnMucHVzaCh3b3JkKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgbW9kcyA9IHt9O1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IGZhbHNlO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIgPSBzdWJwYXRoO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IHRydWU7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIgPSB0b2tlbml6ZShzdWJwYXRoKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAocmVjdXIgPT09IFVOREVGKXsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyLmV4ZWMgPSBjbG9zZXIuZXhlYztcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ci5kb0VhY2ggPSBkb0VhY2g7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBjb2xsZWN0aW9uLnB1c2gocmVjdXIpO1xuICAgICAgICAgICAgICAgICAgICAgICAgdG9rZW5zLnB1c2goeyd0dCc6Y29sbGVjdGlvbiwgJ2RvRWFjaCc6ZG9FYWNofSk7XG4gICAgICAgICAgICAgICAgICAgICAgICBjb2xsZWN0aW9uID0gW107XG4gICAgICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IGZhbHNlO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIC8vIFNpbXBsZSBwcm9wZXJ0eSBjb250YWluZXIgaXMgZXF1aXZhbGVudCB0byBkb3Qtc2VwYXJhdGVkIHRva2VuLiBKdXN0IGFkZCB0aGlzIHRva2VuIHRvIHRva2Vucy5cbiAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAoY2xvc2VyLmV4ZWMgPT09ICRQUk9QRVJUWSl7XG4gICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHt0OltzdHJpcFF1b3RlcyhzdWJwYXRoKV19O1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGRvRWFjaCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgdG9rZW5zLnB1c2goeyd3JzpyZWN1ci50WzBdLCAnbW9kcyc6e30sICdkb0VhY2gnOnRydWV9KTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IGZhbHNlO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGRvRWFjaCA9IGZhbHNlOyAvLyByZXNldFxuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgdG9rZW5zLnB1c2gocmVjdXIudFswXSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgc2ltcGxlUGF0aCAmPSB0cnVlO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIC8vIFF1b3RlZCBzdWJwYXRoIGlzIGFsbCB0YWtlbiBsaXRlcmFsbHkgd2l0aG91dCB0b2tlbiBldmFsdWF0aW9uLiBKdXN0IGFkZCBzdWJwYXRoIHRvIHRva2VucyBhcy1pcy5cbiAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAoY2xvc2VyLmV4ZWMgPT09ICRTSU5HTEVRVU9URSB8fCBjbG9zZXIuZXhlYyA9PT0gJERPVUJMRVFVT1RFKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChtb2RzLmhhcyl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgd29yZCA9IHsndyc6IHN1YnBhdGgsICdtb2RzJzogbW9kcywgJ2RvRWFjaCc6IGRvRWFjaH07XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gdG9rZW5zLnB1c2god29yZCk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgbW9kcyA9IHt9O1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gZmFsc2U7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB0b2tlbnMucHVzaChzdWJwYXRoKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IHRydWU7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgLy8gT3RoZXJ3aXNlLCBjcmVhdGUgdG9rZW4gb2JqZWN0IHRvIGhvbGQgdG9rZW5pemVkIHN1YnBhdGgsIGFkZCB0byB0b2tlbnMuXG4gICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKHN1YnBhdGggPT09ICcnKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHt0OltdLHNpbXBsZTp0cnVlfTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyID0gdG9rZW5pemUoc3VicGF0aCk7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAocmVjdXIgPT09IFVOREVGKXsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIuZXhlYyA9IGNsb3Nlci5leGVjO1xuICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIuZG9FYWNoID0gZG9FYWNoO1xuICAgICAgICAgICAgICAgICAgICAgICAgdG9rZW5zLnB1c2gocmVjdXIpO1xuICAgICAgICAgICAgICAgICAgICAgICAgc2ltcGxlUGF0aCAmPSBmYWxzZTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICBzdWJwYXRoID0gJyc7IC8vIHJlc2V0IHN1YnBhdGhcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICAvLyBJZiBhIHByZWZpeCBjaGFyYWN0ZXIgaXMgZm91bmQsIHN0b3JlIGl0IGluIGBtb2RzYCBmb3IgbGF0ZXIgcmVmZXJlbmNlLlxuICAgICAgICAgICAgLy8gTXVzdCBrZWVwIGNvdW50IGR1ZSB0byBgcGFyZW50YCBwcmVmaXggdGhhdCBjYW4gYmUgdXNlZCBtdWx0aXBsZSB0aW1lcyBpbiBvbmUgdG9rZW4uXG4gICAgICAgICAgICBlbHNlIGlmICghZXNjYXBlZCAmJiBwYXRoW2ldIGluIG9wdC5wcmVmaXhlcyAmJiBvcHQucHJlZml4ZXNbcGF0aFtpXV0uZXhlYyl7XG4gICAgICAgICAgICAgICAgbW9kcy5oYXMgPSB0cnVlO1xuICAgICAgICAgICAgICAgIGlmIChtb2RzW29wdC5wcmVmaXhlc1twYXRoW2ldXS5leGVjXSkgeyBtb2RzW29wdC5wcmVmaXhlc1twYXRoW2ldXS5leGVjXSsrOyB9XG4gICAgICAgICAgICAgICAgZWxzZSB7IG1vZHNbb3B0LnByZWZpeGVzW3BhdGhbaV1dLmV4ZWNdID0gMTsgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgLy8gSWYgYSBzZXBhcmF0b3IgaXMgZm91bmQsIHRpbWUgdG8gc3RvcmUgdGhlIHRva2VuIHdlJ3ZlIGJlZW4gYWNjdW11bGF0aW5nLiBJZlxuICAgICAgICAgICAgLy8gdGhpcyB0b2tlbiBoYWQgYSBwcmVmaXgsIHdlIHN0b3JlIHRoZSB0b2tlbiBhcyBhbiBvYmplY3Qgd2l0aCBtb2RpZmllciBkYXRhLlxuICAgICAgICAgICAgLy8gSWYgdGhlIHNlcGFyYXRvciBpcyB0aGUgY29sbGVjdGlvbiBzZXBhcmF0b3IsIHdlIG11c3QgZWl0aGVyIGNyZWF0ZSBvciBhZGRcbiAgICAgICAgICAgIC8vIHRvIGEgY29sbGVjdGlvbiBmb3IgdGhpcyB0b2tlbi4gRm9yIHNpbXBsZSBzZXBhcmF0b3IsIHdlIGVpdGhlciBhZGQgdGhlIHRva2VuXG4gICAgICAgICAgICAvLyB0byB0aGUgdG9rZW4gbGlzdCBvciBlbHNlIGFkZCB0byB0aGUgZXhpc3RpbmcgY29sbGVjdGlvbiBpZiBpdCBleGlzdHMuXG4gICAgICAgICAgICBlbHNlIGlmICghZXNjYXBlZCAmJiBvcHQuc2VwYXJhdG9yc1twYXRoW2ldXSAmJiBvcHQuc2VwYXJhdG9yc1twYXRoW2ldXS5leGVjKXtcbiAgICAgICAgICAgICAgICBzZXBhcmF0b3IgPSBvcHQuc2VwYXJhdG9yc1twYXRoW2ldXTtcbiAgICAgICAgICAgICAgICBpZiAoIXdvcmQgJiYgKG1vZHMuaGFzIHx8IGhhc1dpbGRjYXJkKSl7XG4gICAgICAgICAgICAgICAgICAgIC8vIGZvdW5kIGEgc2VwYXJhdG9yLCBhZnRlciBzZWVpbmcgcHJlZml4ZXMsIGJ1dCBubyB0b2tlbiB3b3JkIC0+IGludmFsaWRcbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuIHVuZGVmaW5lZDtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgLy8gVGhpcyB0b2tlbiB3aWxsIHJlcXVpcmUgc3BlY2lhbCBpbnRlcnByZXRlciBwcm9jZXNzaW5nIGR1ZSB0byBwcmVmaXggb3Igd2lsZGNhcmQuXG4gICAgICAgICAgICAgICAgaWYgKHdvcmQgJiYgKG1vZHMuaGFzIHx8IGhhc1dpbGRjYXJkIHx8IGRvRWFjaCkpe1xuICAgICAgICAgICAgICAgICAgICB3b3JkID0geyd3Jzogd29yZCwgJ21vZHMnOiBtb2RzLCAnZG9FYWNoJzogZG9FYWNofTtcbiAgICAgICAgICAgICAgICAgICAgbW9kcyA9IHt9O1xuICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IGZhbHNlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAvLyB3b3JkIGlzIGEgcGxhaW4gcHJvcGVydHkgb3IgZW5kIG9mIGNvbGxlY3Rpb25cbiAgICAgICAgICAgICAgICBpZiAoc2VwYXJhdG9yLmV4ZWMgPT09ICRQUk9QRVJUWSB8fCBzZXBhcmF0b3IuZXhlYyA9PT0gJEVBQ0gpe1xuICAgICAgICAgICAgICAgICAgICAvLyB3ZSBhcmUgZ2F0aGVyaW5nIGEgY29sbGVjdGlvbiwgc28gYWRkIGxhc3Qgd29yZCB0byBjb2xsZWN0aW9uIGFuZCB0aGVuIHN0b3JlXG4gICAgICAgICAgICAgICAgICAgIGlmIChjb2xsZWN0aW9uWzBdICE9PSBVTkRFRil7XG4gICAgICAgICAgICAgICAgICAgICAgICB3b3JkICYmIGNvbGxlY3Rpb24ucHVzaCh3b3JkKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIHRva2Vucy5wdXNoKHsndHQnOmNvbGxlY3Rpb24sICdkb0VhY2gnOmRvRWFjaH0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgY29sbGVjdGlvbiA9IFtdOyAvLyByZXNldFxuICAgICAgICAgICAgICAgICAgICAgICAgc2ltcGxlUGF0aCAmPSBmYWxzZTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAvLyB3b3JkIGlzIGEgcGxhaW4gcHJvcGVydHlcbiAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICB3b3JkICYmIHRva2Vucy5wdXNoKHdvcmQpO1xuICAgICAgICAgICAgICAgICAgICAgICAgc2ltcGxlUGF0aCAmPSB0cnVlO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIC8vIElmIHRoZSBzZXBhcmF0b3IgaXMgdGhlIFwiZWFjaFwiIHNlcGFydG9yLCB0aGUgZm9sbG93aW5nIHdvcmQgd2lsbCBiZSBldmFsdWF0ZWQgZGlmZmVyZW50bHkuXG4gICAgICAgICAgICAgICAgICAgIC8vIElmIGl0J3Mgbm90IHRoZSBcImVhY2hcIiBzZXBhcmF0b3IsIHRoZW4gcmVzZXQgXCJkb0VhY2hcIlxuICAgICAgICAgICAgICAgICAgICBkb0VhY2ggPSBzZXBhcmF0b3IuZXhlYyA9PT0gJEVBQ0g7IC8vIHJlc2V0XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIC8vIHdvcmQgaXMgYSBjb2xsZWN0aW9uXG4gICAgICAgICAgICAgICAgZWxzZSBpZiAoc2VwYXJhdG9yLmV4ZWMgPT09ICRDT0xMRUNUSU9OKXtcbiAgICAgICAgICAgICAgICAgICAgd29yZCAmJiBjb2xsZWN0aW9uLnB1c2god29yZCk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIHdvcmQgPSAnJzsgLy8gcmVzZXRcbiAgICAgICAgICAgICAgICBoYXNXaWxkY2FyZCA9IGZhbHNlOyAvLyByZXNldFxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgLy8gRm91bmQgYSBjb250YWluZXIgb3BlbmluZyBjaGFyYWN0ZXIuIEEgY29udGFpbmVyIG9wZW5pbmcgaXMgZXF1aXZhbGVudCB0b1xuICAgICAgICAgICAgLy8gZmluZGluZyBhIHNlcGFyYXRvciwgc28gXCJmb28uYmFyXCIgaXMgZXF1aXZhbGVudCB0byBcImZvb1tiYXJdXCIsIHNvIGFwcGx5IHNpbWlsYXJcbiAgICAgICAgICAgIC8vIHByb2Nlc3MgYXMgc2VwYXJhdG9yIGFib3ZlIHdpdGggcmVzcGVjdCB0byB0b2tlbiB3ZSBoYXZlIGFjY3VtdWxhdGVkIHNvIGZhci5cbiAgICAgICAgICAgIC8vIEV4Y2VwdCBpbiBjYXNlIGNvbGxlY3Rpb25zIC0gcGF0aCBtYXkgaGF2ZSBhIGNvbGxlY3Rpb24gb2YgY29udGFpbmVycywgc29cbiAgICAgICAgICAgIC8vIGluIFwiZm9vW2Jhcl0sW2Jhel1cIiwgdGhlIFwiW2Jhcl1cIiBtYXJrcyB0aGUgZW5kIG9mIHRva2VuIFwiZm9vXCIsIGJ1dCBcIltiYXpdXCIgaXNcbiAgICAgICAgICAgIC8vIG1lcmVseSBhbm90aGVyIGVudHJ5IGluIHRoZSBjb2xsZWN0aW9uLCBzbyB3ZSBkb24ndCBjbG9zZSBvZmYgdGhlIGNvbGxlY3Rpb24gdG9rZW5cbiAgICAgICAgICAgIC8vIHlldC5cbiAgICAgICAgICAgIC8vIFNldCBkZXB0aCB2YWx1ZSBmb3IgZnVydGhlciBwcm9jZXNzaW5nLlxuICAgICAgICAgICAgZWxzZSBpZiAoIWVzY2FwZWQgJiYgb3B0LmNvbnRhaW5lcnNbcGF0aFtpXV0gJiYgb3B0LmNvbnRhaW5lcnNbcGF0aFtpXV0uZXhlYyl7XG4gICAgICAgICAgICAgICAgY2xvc2VyID0gb3B0LmNvbnRhaW5lcnNbcGF0aFtpXV07XG4gICAgICAgICAgICAgICAgaWYgKHdvcmQgJiYgKG1vZHMuaGFzIHx8IGhhc1dpbGRjYXJkIHx8IGRvRWFjaCkpe1xuICAgICAgICAgICAgICAgICAgICBpZiAodHlwZW9mIHdvcmQgPT09ICdzdHJpbmcnKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIHdvcmQgPSB7J3cnOiB3b3JkLCAnbW9kcyc6IG1vZHMsICdkb0VhY2gnOmRvRWFjaH07XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICB3b3JkLm1vZHMgPSBtb2RzO1xuICAgICAgICAgICAgICAgICAgICAgICAgd29yZC5kb0VhY2ggPSBkb0VhY2g7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgbW9kcyA9IHt9O1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBpZiAoY29sbGVjdGlvblswXSAhPT0gVU5ERUYpe1xuICAgICAgICAgICAgICAgICAgICAvLyB3ZSBhcmUgZ2F0aGVyaW5nIGEgY29sbGVjdGlvbiwgc28gYWRkIGxhc3Qgd29yZCB0byBjb2xsZWN0aW9uIGFuZCB0aGVuIHN0b3JlXG4gICAgICAgICAgICAgICAgICAgIHdvcmQgJiYgY29sbGVjdGlvbi5wdXNoKHdvcmQpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gd29yZCBpcyBhIHBsYWluIHByb3BlcnR5XG4gICAgICAgICAgICAgICAgICAgIHdvcmQgJiYgdG9rZW5zLnB1c2god29yZCk7XG4gICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gdHJ1ZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgb3BlbmVyID0gcGF0aFtpXTtcbiAgICAgICAgICAgICAgICAvLyAxKSBkb24ndCByZXNldCBkb0VhY2ggZm9yIGVtcHR5IHdvcmQgYmVjYXVzZSB0aGlzIGlzIFtmb29dPFtiYXJdXG4gICAgICAgICAgICAgICAgLy8gMikgZG9uJ3QgcmVzZXQgZG9FYWNoIGZvciBvcGVuaW5nIENhbGwgYmVjYXVzZSB0aGlzIGlzIGEsYjxmbigpXG4gICAgICAgICAgICAgICAgaWYgKHdvcmQgJiYgb3B0LmNvbnRhaW5lcnNbb3BlbmVyXS5leGVjICE9PSAkQ0FMTCl7XG4gICAgICAgICAgICAgICAgICAgIGRvRWFjaCA9IGZhbHNlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICB3b3JkID0gJyc7XG4gICAgICAgICAgICAgICAgaGFzV2lsZGNhcmQgPSBmYWxzZTtcbiAgICAgICAgICAgICAgICBkZXB0aCsrO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgLy8gT3RoZXJ3aXNlLCB0aGlzIGlzIGp1c3QgYW5vdGhlciBjaGFyYWN0ZXIgdG8gYWRkIHRvIHRoZSBjdXJyZW50IHRva2VuXG4gICAgICAgICAgICBlbHNlIGlmIChpIDwgcGF0aExlbmd0aCkge1xuICAgICAgICAgICAgICAgIHdvcmQgKz0gcGF0aFtpXTtcbiAgICAgICAgICAgIH1cblxuICAgICAgICAgICAgLy8gSWYgY3VycmVudCBwYXRoIGluZGV4IG1hdGNoZXMgdGhlIGVzY2FwZSBpbmRleCB2YWx1ZSwgcmVzZXQgYGVzY2FwZWRgXG4gICAgICAgICAgICBpZiAoaSA8IHBhdGhMZW5ndGggJiYgaSA9PT0gZXNjYXBlZCl7XG4gICAgICAgICAgICAgICAgZXNjYXBlZCA9IDA7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cblxuICAgICAgICAvLyBQYXRoIGVuZGVkIGluIGFuIGVzY2FwZSBjaGFyYWN0ZXJcbiAgICAgICAgaWYgKGVzY2FwZWQpe1xuICAgICAgICAgICAgcmV0dXJuIHVuZGVmaW5lZDtcbiAgICAgICAgfVxuXG4gICAgICAgIC8vIEFkZCB0cmFpbGluZyB3b3JkIHRvIHRva2VucywgaWYgcHJlc2VudFxuICAgICAgICBpZiAodHlwZW9mIHdvcmQgPT09ICdzdHJpbmcnICYmIHdvcmQgJiYgKG1vZHMuaGFzIHx8IGhhc1dpbGRjYXJkIHx8IGRvRWFjaCkpe1xuICAgICAgICAgICAgd29yZCA9IHsndyc6IHdvcmQsICdtb2RzJzogd29yZC5tb2RzIHx8IG1vZHMsICdkb0VhY2gnOiBkb0VhY2h9O1xuICAgICAgICAgICAgbW9kcyA9IHt9O1xuICAgICAgICAgICAgc2ltcGxlUGF0aCAmPSBmYWxzZTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIGlmICh3b3JkICYmIG1vZHMuaGFzKXtcbiAgICAgICAgICAgIHdvcmQubW9kcyA9IG1vZHM7XG4gICAgICAgIH1cbiAgICAgICAgLy8gV2UgYXJlIGdhdGhlcmluZyBhIGNvbGxlY3Rpb24sIHNvIGFkZCBsYXN0IHdvcmQgdG8gY29sbGVjdGlvbiBhbmQgdGhlbiBzdG9yZVxuICAgICAgICBpZiAoY29sbGVjdGlvblswXSAhPT0gVU5ERUYpe1xuICAgICAgICAgICAgd29yZCAmJiBjb2xsZWN0aW9uLnB1c2god29yZCk7XG4gICAgICAgICAgICB0b2tlbnMucHVzaCh7J3R0Jzpjb2xsZWN0aW9uLCAnZG9FYWNoJzpkb0VhY2h9KTtcbiAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gZmFsc2U7XG4gICAgICAgIH1cbiAgICAgICAgLy8gV29yZCBpcyBhIHBsYWluIHByb3BlcnR5XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgd29yZCAmJiB0b2tlbnMucHVzaCh3b3JkKTtcbiAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gdHJ1ZTtcbiAgICAgICAgfVxuXG4gICAgICAgIC8vIGRlcHRoICE9IDAgbWVhbnMgbWlzbWF0Y2hlZCBjb250YWluZXJzXG4gICAgICAgIGlmIChkZXB0aCAhPT0gMCl7IHJldHVybiB1bmRlZmluZWQ7IH1cblxuICAgICAgICAvLyBJZiBwYXRoIHdhcyB2YWxpZCwgY2FjaGUgdGhlIHJlc3VsdFxuICAgICAgICBvcHQudXNlQ2FjaGUgJiYgKGNhY2hlW3N0cl0gPSB7dDogdG9rZW5zLCBzaW1wbGU6IHNpbXBsZVBhdGh9KTtcblxuICAgICAgICByZXR1cm4ge3Q6IHRva2Vucywgc2ltcGxlOiBzaW1wbGVQYXRofTtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogSXQgaXMgYHJlc29sdmVQYXRoYCdzIGpvYiB0byB0cmF2ZXJzZSBhbiBvYmplY3QgYWNjb3JkaW5nIHRvIHRoZSB0b2tlbnNcbiAgICAgKiBkZXJpdmVkIGZyb20gdGhlIGtleXBhdGggYW5kIGVpdGhlciByZXR1cm4gdGhlIHZhbHVlIGZvdW5kIHRoZXJlIG9yIHNldFxuICAgICAqIGEgbmV3IHZhbHVlIGluIHRoYXQgbG9jYXRpb24uXG4gICAgICogVGhlIHRva2VucyBhcmUgYSBzaW1wbGUgYXJyYXkgYW5kIGByZW9zbHZlUGF0aGAgbG9vcHMgdGhyb3VnaCB0aGUgbGlzdFxuICAgICAqIHdpdGggYSBzaW1wbGUgXCJ3aGlsZVwiIGxvb3AuIEEgdG9rZW4gbWF5IGl0c2VsZiBiZSBhIG5lc3RlZCB0b2tlbiBhcnJheSxcbiAgICAgKiB3aGljaCBpcyBwcm9jZXNzZWQgdGhyb3VnaCByZWN1cnNpb24uXG4gICAgICogQXMgZWFjaCBzdWNjZXNzaXZlIHZhbHVlIGlzIHJlc29sdmVkIHdpdGhpbiBgb2JqYCwgdGhlIGN1cnJlbnQgdmFsdWUgaXNcbiAgICAgKiBwdXNoZWQgb250byB0aGUgXCJ2YWx1ZVN0YWNrXCIsIGVuYWJsaW5nIGJhY2t3YXJkIHJlZmVyZW5jZXMgKHVwd2FyZHMgaW4gYG9iamApXG4gICAgICogdGhyb3VnaCBwYXRoIHByZWZpeGVzIGxpa2UgXCI8XCIgZm9yIFwicGFyZW50XCIgYW5kIFwiflwiIGZvciBcInJvb3RcIi4gVGhlIGxvb3BcbiAgICAgKiBzaG9ydC1jaXJjdWl0cyBieSByZXR1cm5pbmcgYHVuZGVmaW5lZGAgaWYgdGhlIHBhdGggaXMgaW52YWxpZCBhdCBhbnkgcG9pbnQsXG4gICAgICogZXhjZXB0IGluIGBzZXRgIHNjZW5hcmlvIHdpdGggYGZvcmNlYCBlbmFibGVkLlxuICAgICAqIEBwcml2YXRlXG4gICAgICogQHBhcmFtICB7T2JqZWN0fSBvYmogICAgICAgIFRoZSBkYXRhIG9iamVjdCB0byBiZSByZWFkL3dyaXR0ZW5cbiAgICAgKiBAcGFyYW0gIHtTdHJpbmd9IHBhdGggICAgICAgVGhlIGtleXBhdGggd2hpY2ggYHJlc29sdmVQYXRoYCB3aWxsIGV2YWx1YXRlIGFnYWluc3QgYG9iamAuIE1heSBiZSBhIHByZS1jb21waWxlZCBUb2tlbnMgc2V0IGluc3RlYWQgb2YgYSBzdHJpbmcuXG4gICAgICogQHBhcmFtICB7QW55fSBuZXdWYWx1ZSAgIFRoZSBuZXcgdmFsdWUgdG8gc2V0IGF0IHRoZSBwb2ludCBkZXNjcmliZWQgYnkgYHBhdGhgLiBVbmRlZmluZWQgaWYgdXNlZCBpbiBgZ2V0YCBzY2VuYXJpby5cbiAgICAgKiBAcGFyYW0gIHtBcnJheX0gYXJncyAgICAgICBBcnJheSBvZiBleHRyYSBhcmd1bWVudHMgd2hpY2ggbWF5IGJlIHJlZmVyZW5jZWQgYnkgcGxhY2Vob2xkZXJzLiBVbmRlZmluZWQgaWYgbm8gZXh0cmEgYXJndW1lbnRzIHdlcmUgZ2l2ZW4uXG4gICAgICogQHBhcmFtICB7QXJyYXl9IHZhbHVlU3RhY2sgU3RhY2sgb2Ygb2JqZWN0IGNvbnRleHRzIGFjY3VtdWxhdGVkIGFzIHRoZSBwYXRoIHRva2VucyBhcmUgcHJvY2Vzc2VkIGluIGBvYmpgXG4gICAgICogQHJldHVybiB7QW55fSAgICAgICAgICAgIEluIGBnZXRgLCByZXR1cm5zIHRoZSB2YWx1ZSBmb3VuZCBpbiBgb2JqYCBhdCBgcGF0aGAuIEluIGBzZXRgLCByZXR1cm5zIHRoZSBuZXcgdmFsdWUgdGhhdCB3YXMgc2V0IGluIGBvYmpgLiBJZiBgZ2V0YCBvciBgc2V0YCBhcmUgbnRvIHN1Y2Nlc3NmdWwsIHJldHVybnMgYHVuZGVmaW5lZGBcbiAgICAgKi9cbiAgICB2YXIgcmVzb2x2ZVBhdGggPSBmdW5jdGlvbiAob2JqLCBwYXRoLCBuZXdWYWx1ZSwgYXJncywgdmFsdWVTdGFjayl7XG4gICAgICAgIHZhciBjaGFuZ2UgPSBuZXdWYWx1ZSAhPT0gVU5ERUYsIC8vIGFyZSB3ZSBzZXR0aW5nIGEgbmV3IHZhbHVlP1xuICAgICAgICAgICAgdGsgPSBbXSxcbiAgICAgICAgICAgIHRrTGVuZ3RoID0gMCxcbiAgICAgICAgICAgIHRrTGFzdElkeCA9IDAsXG4gICAgICAgICAgICB2YWx1ZVN0YWNrTGVuZ3RoID0gMSxcbiAgICAgICAgICAgIGkgPSAwLCBqID0gMCxcbiAgICAgICAgICAgIHByZXYgPSBvYmosXG4gICAgICAgICAgICBjdXJyID0gJycsXG4gICAgICAgICAgICBjdXJyTGVuZ3RoID0gMCxcbiAgICAgICAgICAgIGVhY2hMZW5ndGggPSAwLFxuICAgICAgICAgICAgd29yZENvcHkgPSAnJyxcbiAgICAgICAgICAgIGNvbnRleHRQcm9wLFxuICAgICAgICAgICAgaWR4ID0gMCxcbiAgICAgICAgICAgIGNvbnRleHQgPSBvYmosXG4gICAgICAgICAgICByZXQsXG4gICAgICAgICAgICBuZXdWYWx1ZUhlcmUgPSBmYWxzZSxcbiAgICAgICAgICAgIHBsYWNlSW50ID0gMCxcbiAgICAgICAgICAgIHByb3AgPSAnJyxcbiAgICAgICAgICAgIGNhbGxBcmdzO1xuXG4gICAgICAgIC8vIEZvciBTdHJpbmcgcGF0aCwgZWl0aGVyIGZldGNoIHRva2VucyBmcm9tIGNhY2hlIG9yIGZyb20gYHRva2VuaXplYC5cbiAgICAgICAgaWYgKHR5cGVvZiBwYXRoID09PSAkU1RSSU5HKXtcbiAgICAgICAgICAgIGlmIChvcHQudXNlQ2FjaGUgJiYgY2FjaGVbcGF0aF0pIHsgdGsgPSBjYWNoZVtwYXRoXS50OyB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB0ayA9IHRva2VuaXplKHBhdGgpO1xuICAgICAgICAgICAgICAgIGlmICh0ayA9PT0gVU5ERUYpeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgICAgICAgICAgdGsgPSB0ay50O1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIC8vIEZvciBhIG5vbi1zdHJpbmcsIGFzc3VtZSBhIHByZS1jb21waWxlZCB0b2tlbiBhcnJheVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHRrID0gcGF0aC50ID8gcGF0aC50IDogW3BhdGhdO1xuICAgICAgICB9XG5cbiAgICAgICAgdGtMZW5ndGggPSB0ay5sZW5ndGg7XG4gICAgICAgIGlmICh0a0xlbmd0aCA9PT0gMCkgeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgIHRrTGFzdElkeCA9IHRrTGVuZ3RoIC0gMTtcblxuICAgICAgICAvLyB2YWx1ZVN0YWNrIHdpbGwgYmUgYW4gYXJyYXkgaWYgd2UgYXJlIHdpdGhpbiBhIHJlY3Vyc2l2ZSBjYWxsIHRvIGByZXNvbHZlUGF0aGBcbiAgICAgICAgaWYgKHZhbHVlU3RhY2spe1xuICAgICAgICAgICAgdmFsdWVTdGFja0xlbmd0aCA9IHZhbHVlU3RhY2subGVuZ3RoO1xuICAgICAgICB9XG4gICAgICAgIC8vIE9uIG9yaWdpbmFsIGVudHJ5IHRvIGByZXNvbHZlUGF0aGAsIGluaXRpYWxpemUgdmFsdWVTdGFjayB3aXRoIHRoZSBiYXNlIG9iamVjdC5cbiAgICAgICAgLy8gdmFsdWVTdGFja0xlbmd0aCB3YXMgYWxyZWFkeSBpbml0aWFsaXplZCB0byAxLlxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHZhbHVlU3RhY2sgPSBbb2JqXTtcbiAgICAgICAgfVxuXG4gICAgICAgIC8vIENvbnZlcnRlZCBBcnJheS5yZWR1Y2UgaW50byB3aGlsZSBsb29wLCBzdGlsbCB1c2luZyBcInByZXZcIiwgXCJjdXJyXCIsIFwiaWR4XCJcbiAgICAgICAgLy8gYXMgbG9vcCB2YWx1ZXNcbiAgICAgICAgd2hpbGUgKHByZXYgIT09IFVOREVGICYmIGlkeCA8IHRrTGVuZ3RoKXtcbiAgICAgICAgICAgIGN1cnIgPSB0a1tpZHhdO1xuXG4gICAgICAgICAgICAvLyBJZiB3ZSBhcmUgc2V0dGluZyBhIG5ldyB2YWx1ZSBhbmQgdGhpcyB0b2tlbiBpcyB0aGUgbGFzdCB0b2tlbiwgdGhpc1xuICAgICAgICAgICAgLy8gaXMgdGhlIHBvaW50IHdoZXJlIHRoZSBuZXcgdmFsdWUgbXVzdCBiZSBzZXQuXG4gICAgICAgICAgICBuZXdWYWx1ZUhlcmUgPSAoY2hhbmdlICYmIChpZHggPT09IHRrTGFzdElkeCkpO1xuXG4gICAgICAgICAgICAvLyBIYW5kbGUgbW9zdCBjb21tb24gc2ltcGxlIHBhdGggc2NlbmFyaW8gZmlyc3RcbiAgICAgICAgICAgIGlmICh0eXBlb2YgY3VyciA9PT0gJFNUUklORyl7XG4gICAgICAgICAgICAgICAgLy8gSWYgd2UgYXJlIHNldHRpbmcuLi5cbiAgICAgICAgICAgICAgICBpZiAoY2hhbmdlKXtcbiAgICAgICAgICAgICAgICAgICAgLy8gSWYgdGhpcyBpcyB0aGUgZmluYWwgdG9rZW4gd2hlcmUgdGhlIG5ldyB2YWx1ZSBnb2VzLCBzZXQgaXRcbiAgICAgICAgICAgICAgICAgICAgaWYgKG5ld1ZhbHVlSGVyZSl7XG4gICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0W2N1cnJdID0gbmV3VmFsdWU7XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoY29udGV4dFtjdXJyXSAhPT0gbmV3VmFsdWUpeyByZXR1cm4gdW5kZWZpbmVkOyB9IC8vIG5ldyB2YWx1ZSBmYWlsZWQgdG8gc2V0XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgLy8gRm9yIGVhcmxpZXIgdG9rZW5zLCBjcmVhdGUgb2JqZWN0IHByb3BlcnRpZXMgaWYgXCJmb3JjZVwiIGlzIGVuYWJsZWRcbiAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAob3B0LmZvcmNlICYmIHR5cGVvZiBjb250ZXh0W2N1cnJdID09PSAndW5kZWZpbmVkJykge1xuICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFtjdXJyXSA9IHt9O1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIC8vIFJldHVybiB2YWx1ZSBpcyBhc3NpZ25lZCBhcyB2YWx1ZSBvZiB0aGlzIG9iamVjdCBwcm9wZXJ0eVxuICAgICAgICAgICAgICAgIHJldCA9IGNvbnRleHRbY3Vycl07XG5cbiAgICAgICAgICAgICAgICAvLyBUaGlzIGJhc2ljIHN0cnVjdHVyZSBpcyByZXBlYXRlZCBpbiBvdGhlciBzY2VuYXJpb3MgYmVsb3csIHNvIHRoZSBsb2dpY1xuICAgICAgICAgICAgICAgIC8vIHBhdHRlcm4gaXMgb25seSBkb2N1bWVudGVkIGhlcmUgZm9yIGJyZXZpdHkuXG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICBpZiAoY3VyciA9PT0gVU5ERUYpe1xuICAgICAgICAgICAgICAgICAgICByZXQgPSB1bmRlZmluZWQ7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGVsc2UgaWYgKGN1cnIudHQpe1xuICAgICAgICAgICAgICAgICAgICAvLyBDYWxsIHJlc29sdmVQYXRoIGFnYWluIHdpdGggYmFzZSB2YWx1ZSBhcyBldmFsdWF0ZWQgdmFsdWUgc28gZmFyIGFuZFxuICAgICAgICAgICAgICAgICAgICAvLyBlYWNoIGVsZW1lbnQgb2YgYXJyYXkgYXMgdGhlIHBhdGguIENvbmNhdCBhbGwgdGhlIHJlc3VsdHMgdG9nZXRoZXIuXG4gICAgICAgICAgICAgICAgICAgIHJldCA9IFtdO1xuICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci5kb0VhY2gpe1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKCFBcnJheS5pc0FycmF5KGNvbnRleHQpKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXR1cm4gdW5kZWZpbmVkO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgaiA9IDA7XG4gICAgICAgICAgICAgICAgICAgICAgICBlYWNoTGVuZ3RoID0gY29udGV4dC5sZW5ndGg7XG5cbiAgICAgICAgICAgICAgICAgICAgICAgIC8vIFBhdGggbGlrZSBBcnJheS0+RWFjaC0+QXJyYXkgcmVxdWlyZXMgYSBuZXN0ZWQgZm9yIGxvb3BcbiAgICAgICAgICAgICAgICAgICAgICAgIC8vIHRvIHByb2Nlc3MgdGhlIHR3byBhcnJheSBsYXllcnMuXG4gICAgICAgICAgICAgICAgICAgICAgICB3aGlsZShqIDwgZWFjaExlbmd0aCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaSA9IDA7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goW10pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGN1cnJMZW5ndGggPSBjdXJyLnR0Lmxlbmd0aDtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB3aGlsZShpIDwgY3Vyckxlbmd0aCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGN1cnIudHRbaV0uZG9FYWNoID0gZmFsc2U7IC8vIFRoaXMgaXMgYSBoYWNrLCBkb24ndCBrbm93IGhvdyBlbHNlIHRvIGRpc2FibGUgXCJkb0VhY2hcIiBmb3IgY29sbGVjdGlvbiBtZW1iZXJzXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChuZXdWYWx1ZUhlcmUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFByb3AgPSByZXNvbHZlUGF0aChjb250ZXh0W2pdLCBjdXJyLnR0W2ldLCBuZXdWYWx1ZSwgYXJncywgdmFsdWVTdGFjayk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAodHlwZW9mIGN1cnIudHRbaV0gPT09ICdzdHJpbmcnKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRQcm9wID0gY29udGV4dFtqXVtjdXJyLnR0W2ldXTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRQcm9wID0gcmVzb2x2ZVBhdGgoY29udGV4dFtqXSwgY3Vyci50dFtpXSwgdW5kZWZpbmVkLCBhcmdzLCB2YWx1ZVN0YWNrKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY29udGV4dFByb3AgPT09IFVOREVGKSB7IHJldHVybiB1bmRlZmluZWQ7IH1cblxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLnR0W2ldLnQgJiYgY3Vyci50dFtpXS5leGVjID09PSAkRVZBTFBST1BFUlRZKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0W2pdW2NvbnRleHRQcm9wXSA9IG5ld1ZhbHVlO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXRbal0ucHVzaChjb250ZXh0UHJvcCk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci50dFtpXS50ICYmIGN1cnIudHRbaV0uZXhlYyA9PT0gJEVWQUxQUk9QRVJUWSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0W2pdLnB1c2goY29udGV4dFtqXVtjb250ZXh0UHJvcF0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXRbal0ucHVzaChjb250ZXh0UHJvcCk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaSsrO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBqKys7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICBpID0gMDtcbiAgICAgICAgICAgICAgICAgICAgICAgIGN1cnJMZW5ndGggPSBjdXJyLnR0Lmxlbmd0aDtcbiAgICAgICAgICAgICAgICAgICAgICAgIHdoaWxlKGkgPCBjdXJyTGVuZ3RoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFByb3AgPSByZXNvbHZlUGF0aChjb250ZXh0LCBjdXJyLnR0W2ldLCBuZXdWYWx1ZSwgYXJncywgdmFsdWVTdGFjayk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKHR5cGVvZiBjdXJyLnR0W2ldID09PSAnc3RyaW5nJyl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRQcm9wID0gY29udGV4dFtjdXJyLnR0W2ldXTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRQcm9wID0gcmVzb2x2ZVBhdGgoY29udGV4dCwgY3Vyci50dFtpXSwgdW5kZWZpbmVkLCBhcmdzLCB2YWx1ZVN0YWNrKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGNvbnRleHRQcm9wID09PSBVTkRFRikgeyByZXR1cm4gdW5kZWZpbmVkOyB9XG5cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIudHRbaV0udCAmJiBjdXJyLnR0W2ldLmV4ZWMgPT09ICRFVkFMUFJPUEVSVFkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFtjb250ZXh0UHJvcF0gPSBuZXdWYWx1ZTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKGNvbnRleHRQcm9wKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIudHRbaV0udCAmJiBjdXJyLnR0W2ldLmV4ZWMgPT09ICRFVkFMUFJPUEVSVFkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goY29udGV4dFtjb250ZXh0UHJvcF0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goY29udGV4dFByb3ApO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGkrKztcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBlbHNlIGlmIChjdXJyLncpe1xuICAgICAgICAgICAgICAgICAgICAvLyB0aGlzIHdvcmQgdG9rZW4gaGFzIG1vZGlmaWVyc1xuICAgICAgICAgICAgICAgICAgICB3b3JkQ29weSA9IGN1cnIudztcbiAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIubW9kcy5oYXMpe1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIubW9kcy5wYXJlbnQpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIG1vZGlmeSBjdXJyZW50IGNvbnRleHQsIHNoaWZ0IHVwd2FyZHMgaW4gYmFzZSBvYmplY3Qgb25lIGxldmVsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dCA9IHZhbHVlU3RhY2tbdmFsdWVTdGFja0xlbmd0aCAtIDEgLSBjdXJyLm1vZHMucGFyZW50XTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY29udGV4dCA9PT0gVU5ERUYpIHsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIubW9kcy5yb290KXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBSZXNldCBjb250ZXh0IGFuZCB2YWx1ZVN0YWNrLCBzdGFydCBvdmVyIGF0IHJvb3QgaW4gdGhpcyBjb250ZXh0XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dCA9IHZhbHVlU3RhY2tbMF07XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgdmFsdWVTdGFjayA9IFtjb250ZXh0XTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB2YWx1ZVN0YWNrTGVuZ3RoID0gMTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLm1vZHMucGxhY2Vob2xkZXIpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHBsYWNlSW50ID0gd29yZENvcHkgLSAxO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChhcmdzW3BsYWNlSW50XSA9PT0gVU5ERUYpeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gRm9yY2UgYXJnc1twbGFjZUludF0gdG8gU3RyaW5nLCB3b24ndCBhdHRlbXB0IHRvIHByb2Nlc3NcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBhcmcgb2YgdHlwZSBmdW5jdGlvbiwgYXJyYXksIG9yIHBsYWluIG9iamVjdFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHdvcmRDb3B5ID0gYXJnc1twbGFjZUludF0udG9TdHJpbmcoKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuXG4gICAgICAgICAgICAgICAgICAgIC8vIGRvRWFjaCBvcHRpb24gbWVhbnMgdG8gdGFrZSBhbGwgdmFsdWVzIGluIGNvbnRleHQgKG11c3QgYmUgYW4gYXJyYXkpLCBhcHBseVxuICAgICAgICAgICAgICAgICAgICAvLyBcImN1cnJcIiB0byBlYWNoIG9uZSwgYW5kIHJldHVybiB0aGUgbmV3IGFycmF5LiBPcGVyYXRlcyBsaWtlIEFycmF5Lm1hcC5cbiAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIuZG9FYWNoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmICghQXJyYXkuaXNBcnJheShjb250ZXh0KSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0dXJuIHVuZGVmaW5lZDtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIHJldCA9IFtdO1xuICAgICAgICAgICAgICAgICAgICAgICAgaSA9IDA7XG4gICAgICAgICAgICAgICAgICAgICAgICBlYWNoTGVuZ3RoID0gY29udGV4dC5sZW5ndGg7XG4gICAgICAgICAgICAgICAgICAgICAgICB3aGlsZShpIDwgZWFjaExlbmd0aCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gXCJjb250ZXh0XCIgbW9kaWZpZXIgKFwiQFwiIGJ5IGRlZmF1bHQpIHJlcGxhY2VzIGN1cnJlbnQgY29udGV4dCB3aXRoIGEgdmFsdWUgZnJvbVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIHRoZSBhcmd1bWVudHMuXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIubW9kcy5jb250ZXh0KXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGlzRGlnaXRzKHdvcmRDb3B5KSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBwbGFjZUludCA9IHdvcmRDb3B5IC0gMTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChhcmdzW3BsYWNlSW50XSA9PT0gVU5ERUYpeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBGb3JjZSBhcmdzW3BsYWNlSW50XSB0byBTdHJpbmcsIHdvbid0IGF0d29yZENvcHl0IHRvIHByb2Nlc3NcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIGFyZyBvZiB0eXBlIGZ1bmN0aW9uLCBhcnJheSwgb3IgcGxhaW4gb2JqZWN0XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChhcmdzW3BsYWNlSW50XSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQgPSB3b3JkQ29weTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gUmVwZWF0IGJhc2ljIHN0cmluZyBwcm9wZXJ0eSBwcm9jZXNzaW5nIHdpdGggd29yZCBhbmQgbW9kaWZpZWQgY29udGV4dFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY29udGV4dFtpXVt3b3JkQ29weV0gIT09IFVOREVGKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXsgY29udGV4dFtpXVt3b3JkQ29weV0gPSBuZXdWYWx1ZTsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goY29udGV4dFtpXVt3b3JkQ29weV0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKHR5cGVvZiBjb250ZXh0W2ldID09PSAnZnVuY3Rpb24nKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKHdvcmRDb3B5KTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBQbGFpbiBwcm9wZXJ0eSB0b2tlbnMgYXJlIGxpc3RlZCBhcyBzcGVjaWFsIHdvcmQgdG9rZW5zIHdoZW5ldmVyXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIGEgd2lsZGNhcmQgaXMgZm91bmQgd2l0aGluIHRoZSBwcm9wZXJ0eSBzdHJpbmcuIEEgd2lsZGNhcmQgaW4gYVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBwcm9wZXJ0eSBjYXVzZXMgYW4gYXJyYXkgb2YgbWF0Y2hpbmcgcHJvcGVydGllcyB0byBiZSByZXR1cm5lZCxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gc28gbG9vcCB0aHJvdWdoIGFsbCBwcm9wZXJ0aWVzIGFuZCBldmFsdWF0ZSB0b2tlbiBmb3IgZXZlcnlcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gcHJvcGVydHkgd2hlcmUgYHdpbGRDYXJkTWF0Y2hgIHJldHVybnMgdHJ1ZS5cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAod2lsZGNhcmRSZWdFeC50ZXN0KHdvcmRDb3B5KSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChbXSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBmb3IgKHByb3AgaW4gY29udGV4dFtpXSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKHdpbGRDYXJkTWF0Y2god29yZENvcHksIHByb3ApKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKG5ld1ZhbHVlSGVyZSl7IGNvbnRleHRbaV1bcHJvcF0gPSBuZXdWYWx1ZTsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXRbaV0ucHVzaChjb250ZXh0W2ldW3Byb3BdKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaSsrO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgLy8gXCJjb250ZXh0XCIgbW9kaWZpZXIgKFwiQFwiIGJ5IGRlZmF1bHQpIHJlcGxhY2VzIGN1cnJlbnQgY29udGV4dCB3aXRoIGEgdmFsdWUgZnJvbVxuICAgICAgICAgICAgICAgICAgICAgICAgLy8gdGhlIGFyZ3VtZW50cy5cbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLm1vZHMuY29udGV4dCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGlzRGlnaXRzKHdvcmRDb3B5KSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHBsYWNlSW50ID0gd29yZENvcHkgLSAxO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoYXJnc1twbGFjZUludF0gPT09IFVOREVGKXsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBGb3JjZSBhcmdzW3BsYWNlSW50XSB0byBTdHJpbmcsIHdvbid0IGF0d29yZENvcHl0IHRvIHByb2Nlc3NcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gYXJnIG9mIHR5cGUgZnVuY3Rpb24sIGFycmF5LCBvciBwbGFpbiBvYmplY3RcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gYXJnc1twbGFjZUludF07XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gd29yZENvcHk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gUmVwZWF0IGJhc2ljIHN0cmluZyBwcm9wZXJ0eSBwcm9jZXNzaW5nIHdpdGggd29yZCBhbmQgbW9kaWZpZWQgY29udGV4dFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjb250ZXh0W3dvcmRDb3B5XSAhPT0gVU5ERUYpIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKG5ld1ZhbHVlSGVyZSl7IGNvbnRleHRbd29yZENvcHldID0gbmV3VmFsdWU7IH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gY29udGV4dFt3b3JkQ29weV07XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKHR5cGVvZiBjb250ZXh0ID09PSAnZnVuY3Rpb24nKXtcblxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQgPSB3b3JkQ29weTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gUGxhaW4gcHJvcGVydHkgdG9rZW5zIGFyZSBsaXN0ZWQgYXMgc3BlY2lhbCB3b3JkIHRva2VucyB3aGVuZXZlclxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIGEgd2lsZGNhcmQgaXMgZm91bmQgd2l0aGluIHRoZSBwcm9wZXJ0eSBzdHJpbmcuIEEgd2lsZGNhcmQgaW4gYVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIHByb3BlcnR5IGNhdXNlcyBhbiBhcnJheSBvZiBtYXRjaGluZyBwcm9wZXJ0aWVzIHRvIGJlIHJldHVybmVkLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIHNvIGxvb3AgdGhyb3VnaCBhbGwgcHJvcGVydGllcyBhbmQgZXZhbHVhdGUgdG9rZW4gZm9yIGV2ZXJ5XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gcHJvcGVydHkgd2hlcmUgYHdpbGRDYXJkTWF0Y2hgIHJldHVybnMgdHJ1ZS5cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIGlmICh3aWxkY2FyZFJlZ0V4LnRlc3Qod29yZENvcHkpKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gW107XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGZvciAocHJvcCBpbiBjb250ZXh0KXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmICh3aWxkQ2FyZE1hdGNoKHdvcmRDb3B5LCBwcm9wKSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKG5ld1ZhbHVlSGVyZSl7IGNvbnRleHRbcHJvcF0gPSBuZXdWYWx1ZTsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKGNvbnRleHRbcHJvcF0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2UgeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgLy8gRXZhbCBQcm9wZXJ0eSB0b2tlbnMgb3BlcmF0ZSBvbiBhIHRlbXBvcmFyeSBjb250ZXh0IGNyZWF0ZWQgYnlcbiAgICAgICAgICAgICAgICAvLyByZWN1cnNpdmVseSBjYWxsaW5nIGByZXNvbHZlUGF0aGAgd2l0aCBhIGNvcHkgb2YgdGhlIHZhbHVlU3RhY2suXG4gICAgICAgICAgICAgICAgZWxzZSBpZiAoY3Vyci5leGVjID09PSAkRVZBTFBST1BFUlRZKXtcbiAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIuZG9FYWNoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmICghQXJyYXkuaXNBcnJheShjb250ZXh0KSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0dXJuIHVuZGVmaW5lZDtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIHJldCA9IFtdO1xuICAgICAgICAgICAgICAgICAgICAgICAgaSA9IDA7XG4gICAgICAgICAgICAgICAgICAgICAgICBlYWNoTGVuZ3RoID0gY29udGV4dC5sZW5ndGg7XG4gICAgICAgICAgICAgICAgICAgICAgICB3aGlsZShpIDwgZWFjaExlbmd0aCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIuc2ltcGxlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKG5ld1ZhbHVlSGVyZSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0W2ldW190aGlzLmdldChjb250ZXh0W2ldLCB7dDpjdXJyLnQsIHNpbXBsZTp0cnVlfSldID0gbmV3VmFsdWU7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goY29udGV4dFtpXVtfdGhpcy5nZXQoY29udGV4dFtpXSwge3Q6Y3Vyci50LCBzaW1wbGU6dHJ1ZX0pXSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRbaV1bcmVzb2x2ZVBhdGgoY29udGV4dFtpXSwgY3VyciwgVU5ERUYsIGFyZ3MsIHZhbHVlU3RhY2spXSA9IG5ld1ZhbHVlO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKGNvbnRleHRbaV1bcmVzb2x2ZVBhdGgoY29udGV4dFtpXSwgY3VyciwgVU5ERUYsIGFyZ3MsIHZhbHVlU3RhY2spXSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGkrKztcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLnNpbXBsZSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKG5ld1ZhbHVlSGVyZSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRbX3RoaXMuZ2V0KGNvbnRleHQsIHt0OiBjdXJyLnQsIHNpbXBsZTp0cnVlfSldID0gbmV3VmFsdWU7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldCA9IGNvbnRleHRbX3RoaXMuZ2V0KGNvbnRleHQsIHt0OmN1cnIudCwgc2ltcGxlOnRydWV9KV07XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFtyZXNvbHZlUGF0aChjb250ZXh0LCBjdXJyLCBVTkRFRiwgYXJncywgdmFsdWVTdGFjayldID0gbmV3VmFsdWU7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldCA9IGNvbnRleHRbcmVzb2x2ZVBhdGgoY29udGV4dCwgY3VyciwgVU5ERUYsIGFyZ3MsIHZhbHVlU3RhY2spXTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAvLyBGdW5jdGlvbnMgYXJlIGNhbGxlZCB1c2luZyBgY2FsbGAgb3IgYGFwcGx5YCwgZGVwZW5kaW5nIG9uIHRoZSBzdGF0ZSBvZlxuICAgICAgICAgICAgICAgIC8vIHRoZSBhcmd1bWVudHMgd2l0aGluIHRoZSAoICkgY29udGFpbmVyLiBGdW5jdGlvbnMgYXJlIGV4ZWN1dGVkIHdpdGggXCJ0aGlzXCJcbiAgICAgICAgICAgICAgICAvLyBzZXQgdG8gdGhlIGNvbnRleHQgaW1tZWRpYXRlbHkgcHJpb3IgdG8gdGhlIGZ1bmN0aW9uIGluIHRoZSBzdGFjay5cbiAgICAgICAgICAgICAgICAvLyBGb3IgZXhhbXBsZSwgXCJhLmIuYy5mbigpXCIgaXMgZXF1aXZhbGVudCB0byBvYmouYS5iLmMuZm4uY2FsbChvYmouYS5iLmMpXG4gICAgICAgICAgICAgICAgZWxzZSBpZiAoY3Vyci5leGVjID09PSAkQ0FMTCl7XG4gICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLmRvRWFjaCl7XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoIUFycmF5LmlzQXJyYXkodmFsdWVTdGFja1t2YWx1ZVN0YWNrTGVuZ3RoIC0gMl0pKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXR1cm4gdW5kZWZpbmVkO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gW107XG4gICAgICAgICAgICAgICAgICAgICAgICBpID0gMDtcbiAgICAgICAgICAgICAgICAgICAgICAgIGVhY2hMZW5ndGggPSBjb250ZXh0Lmxlbmd0aDtcbiAgICAgICAgICAgICAgICAgICAgICAgIHdoaWxlKGkgPCBlYWNoTGVuZ3RoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBJZiBmdW5jdGlvbiBjYWxsIGhhcyBhcmd1bWVudHMsIHByb2Nlc3MgdGhvc2UgYXJndW1lbnRzIGFzIGEgbmV3IHBhdGhcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci50ICYmIGN1cnIudC5sZW5ndGgpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjYWxsQXJncyA9IHJlc29sdmVQYXRoKGNvbnRleHQsIGN1cnIsIFVOREVGLCBhcmdzLCB2YWx1ZVN0YWNrKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGNhbGxBcmdzID09PSBVTkRFRil7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChjb250ZXh0W2ldLmFwcGx5KHZhbHVlU3RhY2tbdmFsdWVTdGFja0xlbmd0aCAtIDJdW2ldKSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAoQXJyYXkuaXNBcnJheShjYWxsQXJncykpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goY29udGV4dFtpXS5hcHBseSh2YWx1ZVN0YWNrW3ZhbHVlU3RhY2tMZW5ndGggLSAyXVtpXSwgY2FsbEFyZ3MpKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKGNvbnRleHRbaV0uY2FsbCh2YWx1ZVN0YWNrW3ZhbHVlU3RhY2tMZW5ndGggLSAyXVtpXSwgY2FsbEFyZ3MpKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goY29udGV4dFtpXS5jYWxsKHZhbHVlU3RhY2tbdmFsdWVTdGFja0xlbmd0aCAtIDJdW2ldKSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGkrKztcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIC8vIElmIGZ1bmN0aW9uIGNhbGwgaGFzIGFyZ3VtZW50cywgcHJvY2VzcyB0aG9zZSBhcmd1bWVudHMgYXMgYSBuZXcgcGF0aFxuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIudCAmJiBjdXJyLnQubGVuZ3RoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci5zaW1wbGUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjYWxsQXJncyA9IF90aGlzLmdldChjb250ZXh0LCBjdXJyKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNhbGxBcmdzID0gcmVzb2x2ZVBhdGgoY29udGV4dCwgY3VyciwgVU5ERUYsIGFyZ3MsIHZhbHVlU3RhY2spO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY2FsbEFyZ3MgPT09IFVOREVGKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gY29udGV4dC5hcHBseSh2YWx1ZVN0YWNrW3ZhbHVlU3RhY2tMZW5ndGggLSAyXSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKEFycmF5LmlzQXJyYXkoY2FsbEFyZ3MpKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gY29udGV4dC5hcHBseSh2YWx1ZVN0YWNrW3ZhbHVlU3RhY2tMZW5ndGggLSAyXSwgY2FsbEFyZ3MpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gY29udGV4dC5jYWxsKHZhbHVlU3RhY2tbdmFsdWVTdGFja0xlbmd0aCAtIDJdLCBjYWxsQXJncyk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gY29udGV4dC5jYWxsKHZhbHVlU3RhY2tbdmFsdWVTdGFja0xlbmd0aCAtIDJdKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIC8vIEFkZCB0aGUgcmV0dXJuIHZhbHVlIHRvIHRoZSBzdGFjayBpbiBjYXNlIHdlIG11c3QgbG9vcCBhZ2Fpbi5cbiAgICAgICAgICAgIC8vIFJlY3Vyc2l2ZSBjYWxscyBwYXNzIHRoZSBzYW1lIHZhbHVlU3RhY2sgYXJyYXkgYXJvdW5kLCBidXQgd2UgZG9uJ3Qgd2FudCB0b1xuICAgICAgICAgICAgLy8gcHVzaCBlbnRyaWVzIG9uIHRoZSBzdGFjayBpbnNpZGUgYSByZWN1cnNpb24sIHNvIGluc3RlYWQgdXNlIGZpeGVkIGFycmF5XG4gICAgICAgICAgICAvLyBpbmRleCByZWZlcmVuY2VzIGJhc2VkIG9uIHdoYXQgKip0aGlzKiogZXhlY3V0aW9uIGtub3dzIHRoZSB2YWx1ZVN0YWNrTGVuZ3RoXG4gICAgICAgICAgICAvLyBzaG91bGQgYmUuIFRoYXQgd2F5LCBpZiBhIHJlY3Vyc2lvbiBhZGRzIG5ldyBlbGVtZW50cywgYW5kIHRoZW4gd2UgYmFjayBvdXQsXG4gICAgICAgICAgICAvLyB0aGlzIGNvbnRleHQgd2lsbCByZW1lbWJlciB0aGUgb2xkIHN0YWNrIGxlbmd0aCBhbmQgd2lsbCBtZXJlbHkgb3ZlcndyaXRlXG4gICAgICAgICAgICAvLyB0aG9zZSBhZGRlZCBlbnRyaWVzLCBpZ25vcmluZyB0aGF0IHRoZXkgd2VyZSB0aGVyZSBpbiB0aGUgZmlyc3QgcGxhY2UuXG4gICAgICAgICAgICB2YWx1ZVN0YWNrW3ZhbHVlU3RhY2tMZW5ndGgrK10gPSByZXQ7XG4gICAgICAgICAgICBjb250ZXh0ID0gcmV0O1xuICAgICAgICAgICAgcHJldiA9IHJldDtcbiAgICAgICAgICAgIGlkeCsrO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBjb250ZXh0O1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBTaW1wbGlmaWVkIHBhdGggZXZhbHVhdGlvbiBoZWF2aWx5IG9wdGltaXplZCBmb3IgcGVyZm9ybWFuY2Ugd2hlblxuICAgICAqIHByb2Nlc3NpbmcgcGF0aHMgd2l0aCBvbmx5IHByb3BlcnR5IG5hbWVzIG9yIGluZGljZXMgYW5kIHNlcGFyYXRvcnMuXG4gICAgICogSWYgdGhlIHBhdGggY2FuIGJlIGNvcnJlY3RseSBwcm9jZXNzZWQgd2l0aCBcInBhdGguc3BsaXQoc2VwYXJhdG9yKVwiLFxuICAgICAqIHRoaXMgZnVuY3Rpb24gd2lsbCBkbyBzby4gQW55IG90aGVyIHNwZWNpYWwgY2hhcmFjdGVycyBmb3VuZCBpbiB0aGVcbiAgICAgKiBwYXRoIHdpbGwgY2F1c2UgdGhlIHBhdGggdG8gYmUgZXZhbHVhdGVkIHdpdGggdGhlIGZ1bGwgYHJlc29sdmVQYXRoYFxuICAgICAqIGZ1bmN0aW9uIGluc3RlYWQuXG4gICAgICogQHByaXZhdGVcbiAgICAgKiBAcGFyYW0gIHtPYmplY3R9IG9iaiAgICAgICAgVGhlIGRhdGEgb2JqZWN0IHRvIGJlIHJlYWQvd3JpdHRlblxuICAgICAqIEBwYXJhbSAge1N0cmluZ30gcGF0aCAgICAgICBUaGUga2V5cGF0aCB3aGljaCBgcmVzb2x2ZVBhdGhgIHdpbGwgZXZhbHVhdGUgYWdhaW5zdCBgb2JqYC5cbiAgICAgKiBAcGFyYW0gIHtBbnl9IG5ld1ZhbHVlICAgVGhlIG5ldyB2YWx1ZSB0byBzZXQgYXQgdGhlIHBvaW50IGRlc2NyaWJlZCBieSBgcGF0aGAuIFVuZGVmaW5lZCBpZiB1c2VkIGluIGBnZXRgIHNjZW5hcmlvLlxuICAgICAqIEByZXR1cm4ge0FueX0gICAgICAgICAgICBJbiBgZ2V0YCwgcmV0dXJucyB0aGUgdmFsdWUgZm91bmQgaW4gYG9iamAgYXQgYHBhdGhgLiBJbiBgc2V0YCwgcmV0dXJucyB0aGUgbmV3IHZhbHVlIHRoYXQgd2FzIHNldCBpbiBgb2JqYC4gSWYgYGdldGAgb3IgYHNldGAgYXJlIG50byBzdWNjZXNzZnVsLCByZXR1cm5zIGB1bmRlZmluZWRgXG4gICAgICovXG4gICAgdmFyIHF1aWNrUmVzb2x2ZVN0cmluZyA9IGZ1bmN0aW9uKG9iaiwgcGF0aCwgbmV3VmFsdWUpe1xuICAgICAgICB2YXIgY2hhbmdlID0gbmV3VmFsdWUgIT09IFVOREVGLFxuICAgICAgICAgICAgdGsgPSBbXSxcbiAgICAgICAgICAgIGkgPSAwLFxuICAgICAgICAgICAgdGtMZW5ndGggPSAwO1xuXG4gICAgICAgIHRrID0gcGF0aC5zcGxpdChwcm9wZXJ0eVNlcGFyYXRvcik7XG4gICAgICAgIG9wdC51c2VDYWNoZSAmJiAoY2FjaGVbcGF0aF0gPSB7dDogdGssIHNpbXBsZTogdHJ1ZX0pO1xuICAgICAgICB0a0xlbmd0aCA9IHRrLmxlbmd0aDtcbiAgICAgICAgd2hpbGUgKG9iaiAhPT0gVU5ERUYgJiYgaSA8IHRrTGVuZ3RoICYmICFpc1Byb3RvdHlwZVBvbGx1dGVkKHRrW2ldKSl7XG4gICAgICAgICAgICBpZiAodGtbaV0gPT09ICcnKXsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgZWxzZSBpZiAoY2hhbmdlKXtcbiAgICAgICAgICAgICAgICBpZiAoaSA9PT0gdGtMZW5ndGggLSAxKXtcbiAgICAgICAgICAgICAgICAgICAgb2JqW3RrW2ldXSA9IG5ld1ZhbHVlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAvLyBGb3IgYXJyYXlzLCB0ZXN0IGN1cnJlbnQgY29udGV4dCBhZ2FpbnN0IHVuZGVmaW5lZCB0byBhdm9pZCBwYXJzaW5nIHRoaXMgc2VnbWVudCBhcyBhIG51bWJlci5cbiAgICAgICAgICAgICAgICAvLyBGb3IgYW55dGhpbmcgZWxzZSwgdXNlIGhhc093blByb3BlcnR5LlxuICAgICAgICAgICAgICAgIGVsc2UgaWYgKG9wdC5mb3JjZSAmJiB0eXBlb2Ygb2JqW3RrW2ldXSA9PT0gJ3VuZGVmaW5lZCcpIHtcbiAgICAgICAgICAgICAgICAgICAgb2JqW3RrW2ldXSA9IHt9O1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIG9iaiA9IG9ialt0a1tpKytdXTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gb2JqO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBTaW1wbGlmaWVkIHBhdGggZXZhbHVhdGlvbiBoZWF2aWx5IG9wdGltaXplZCBmb3IgcGVyZm9ybWFuY2Ugd2hlblxuICAgICAqIHByb2Nlc3NpbmcgYXJyYXkgb2Ygc2ltcGxlIHBhdGggdG9rZW5zIChwbGFpbiBwcm9wZXJ0eSBuYW1lcykuXG4gICAgICogVGhpcyBmdW5jdGlvbiBpcyBlc3NlbnRpYWxseSB0aGUgc2FtZSBhcyBgcXVpY2tSZXNvbHZlU3RyaW5nYCBleGNlcHRcbiAgICAgKiBgcXVpY2tSZXNvbHZlVG9rZW5BcnJheWAgZG9lcyBudG8gbmVlZCB0byBleGVjdXRlIHBhdGguc3BsaXQuXG4gICAgICogQHByaXZhdGVcbiAgICAgKiBAcGFyYW0gIHtPYmplY3R9IG9iaiAgICAgICAgVGhlIGRhdGEgb2JqZWN0IHRvIGJlIHJlYWQvd3JpdHRlblxuICAgICAqIEBwYXJhbSAge0FycmF5fSB0ayAgICAgICBUaGUgdG9rZW4gYXJyYXkgd2hpY2ggYHJlc29sdmVQYXRoYCB3aWxsIGV2YWx1YXRlIGFnYWluc3QgYG9iamAuXG4gICAgICogQHBhcmFtICB7QW55fSBuZXdWYWx1ZSAgIFRoZSBuZXcgdmFsdWUgdG8gc2V0IGF0IHRoZSBwb2ludCBkZXNjcmliZWQgYnkgYHBhdGhgLiBVbmRlZmluZWQgaWYgdXNlZCBpbiBgZ2V0YCBzY2VuYXJpby5cbiAgICAgKiBAcmV0dXJuIHtBbnl9ICAgICAgICAgICAgSW4gYGdldGAsIHJldHVybnMgdGhlIHZhbHVlIGZvdW5kIGluIGBvYmpgIGF0IGBwYXRoYC4gSW4gYHNldGAsIHJldHVybnMgdGhlIG5ldyB2YWx1ZSB0aGF0IHdhcyBzZXQgaW4gYG9iamAuIElmIGBnZXRgIG9yIGBzZXRgIGFyZSBudG8gc3VjY2Vzc2Z1bCwgcmV0dXJucyBgdW5kZWZpbmVkYFxuICAgICAqL1xuICAgIHZhciBxdWlja1Jlc29sdmVUb2tlbkFycmF5ID0gZnVuY3Rpb24ob2JqLCB0aywgbmV3VmFsdWUpe1xuICAgICAgICB2YXIgY2hhbmdlID0gbmV3VmFsdWUgIT09IFVOREVGLFxuICAgICAgICAgICAgaSA9IDAsXG4gICAgICAgICAgICB0a0xlbmd0aCA9IHRrLmxlbmd0aDtcblxuICAgICAgICB3aGlsZSAob2JqICE9IG51bGwgJiYgaSA8IHRrTGVuZ3RoKXtcbiAgICAgICAgICAgIGlmICh0a1tpXSA9PT0gJycpeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgICAgICBlbHNlIGlmIChjaGFuZ2Upe1xuICAgICAgICAgICAgICAgIGlmIChpID09PSB0a0xlbmd0aCAtIDEpe1xuICAgICAgICAgICAgICAgICAgICBvYmpbdGtbaV1dID0gbmV3VmFsdWU7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIC8vIEZvciBhcnJheXMsIHRlc3QgY3VycmVudCBjb250ZXh0IGFnYWluc3QgdW5kZWZpbmVkIHRvIGF2b2lkIHBhcnNpbmcgdGhpcyBzZWdtZW50IGFzIGEgbnVtYmVyLlxuICAgICAgICAgICAgICAgIC8vIEZvciBhbnl0aGluZyBlbHNlLCB1c2UgaGFzT3duUHJvcGVydHkuXG4gICAgICAgICAgICAgICAgZWxzZSBpZiAob3B0LmZvcmNlICYmIHR5cGVvZiBvYmpbdGtbaV1dID09PSAndW5kZWZpbmVkJykge1xuICAgICAgICAgICAgICAgICAgICBvYmpbdGtbaV1dID0ge307XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgb2JqID0gb2JqW3RrW2krK11dO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBvYmo7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIFNlYXJjaGVzIGFuIG9iamVjdCBvciBhcnJheSBmb3IgYSB2YWx1ZSwgYWNjdW11bGF0aW5nIHRoZSBrZXlwYXRoIHRvIHRoZSB2YWx1ZSBhbG9uZ1xuICAgICAqIHRoZSB3YXkuIE9wZXJhdGVzIGluIGEgcmVjdXJzaXZlIHdheSB1bnRpbCBlaXRoZXIgYWxsIGtleXMvaW5kaWNlcyBoYXZlIGJlZW5cbiAgICAgKiBleGhhdXN0ZWQgb3IgYSBtYXRjaCBpcyBmb3VuZC4gUmV0dXJuIHZhbHVlIFwidHJ1ZVwiIG1lYW5zIFwia2VlcCBzY2FubmluZ1wiLCBcImZhbHNlXCJcbiAgICAgKiBtZWFucyBcInN0b3Agbm93XCIuIElmIGEgbWF0Y2ggaXMgZm91bmQsIGluc3RlYWQgb2YgcmV0dXJuaW5nIGEgc2ltcGxlIFwiZmFsc2VcIiwgYVxuICAgICAqIGNhbGxiYWNrIGZ1bmN0aW9uIChzYXZlUGF0aCkgaXMgY2FsbGVkIHdoaWNoIHdpbGwgZGVjaWRlIHdoZXRoZXIgb3Igbm90IHRvIGNvbnRpbnVlXG4gICAgICogdGhlIHNjYW4uIFRoaXMgYWxsb3dzIHRoZSBmdW5jdGlvbiB0byBmaW5kIG9uZSBpbnN0YW5jZSBvZiB2YWx1ZSBvciBhbGwgaW5zdGFuY2VzLFxuICAgICAqIGJhc2VkIG9uIGxvZ2ljIGluIHRoZSBjYWxsYmFjay5cbiAgICAgKiBAcHJpdmF0ZVxuICAgICAqIEBwYXJhbSB7T2JqZWN0fSBvYmogICAgVGhlIGRhdGEgb2JqZWN0IHRvIHNjYW5cbiAgICAgKiBAcGFyYW0ge0FueX0gdmFsIFRoZSB2YWx1ZSB3ZSBhcmUgbG9va2luZyBmb3Igd2l0aGluIGBvYmpgXG4gICAgICogQHBhcmFtIHtGdW5jdGlvbn0gc2F2ZVBhdGggQ2FsbGJhY2sgZnVuY3Rpb24gd2hpY2ggd2lsbCBzdG9yZSBhY2N1bXVsYXRlZCBwYXRocyBhbmQgaW5kaWNhdGUgd2hldGhlciB0byBjb250aW51ZVxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBwYXRoIEFjY3VtdWxhdGVkIGtleXBhdGg7IHVuZGVmaW5lZCBhdCBmaXJzdCwgcG9wdWxhdGVkIGluIHJlY3Vyc2l2ZSBjYWxsc1xuICAgICAqIEBwYXJhbSB7RnVuY3Rpb259IGlzQ2lyY3VsYXJDYiBDYWxsYmFjayBmdW5jdGlvbiB3aGljaCByZXR1cm4gdHJ1ZSBpZiB0aGlzIG9iamVjdCBoYXMgY2lyY3VsYXIgYW5jZXN0cnksIHVzZWQgYnkgYGZpbmRTYWZlKClgXG4gICAgICogQHJldHVybiB7Qm9vbGVhbn0gSW5kaWNhdGVzIHdoZXRoZXIgc2NhbiBwcm9jZXNzIHNob3VsZCBjb250aW51ZSAoXCJ0cnVlXCItPnllcywgXCJmYWxzZVwiLT5ubylcbiAgICAgKi9cbiAgICB2YXIgc2NhbkZvclZhbHVlID0gZnVuY3Rpb24ob2JqLCB2YWwsIHNhdmVQYXRoLCBwYXRoLCBpc0NpcmN1bGFyQ2Ipe1xuICAgICAgICB2YXIgaSwgbGVuLCBtb3JlLCBrZXlzLCBwcm9wO1xuXG4gICAgICAgIGlmICh0eXBlb2YgcGF0aCA9PT0gJFVOREVGSU5FRCl7XG4gICAgICAgICAgICBwYXRoID0gJyc7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAodHlwZW9mIGlzQ2lyY3VsYXJDYiAhPT0gJFVOREVGSU5FRCl7XG4gICAgICAgICAgICBpZiAoaXNDaXJjdWxhckNiKG9iaiwgcGF0aCkpe1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignQ2lyY3VsYXIgb2JqZWN0IHByb3ZpZGVkLiBQYXRoIGF0IFwiJyArIHBhdGggKyAnXCIgbWFrZXMgYSBsb29wLicpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG5cbiAgICAgICAgLy8gSWYgd2UgZm91bmQgdGhlIHZhbHVlIHdlJ3JlIGxvb2tpbmcgZm9yXG4gICAgICAgIGlmIChvYmogPT09IHZhbCl7XG4gICAgICAgICAgICByZXR1cm4gc2F2ZVBhdGgocGF0aCk7IC8vIFNhdmUgdGhlIGFjY3VtdWxhdGVkIHBhdGgsIGFzayB3aGV0aGVyIHRvIGNvbnRpbnVlXG4gICAgICAgIH1cbiAgICAgICAgLy8gVGhpcyBvYmplY3QgaXMgYW4gYXJyYXksIHNvIGV4YW1pbmUgZWFjaCBpbmRleCBzZXBhcmF0ZWx5XG4gICAgICAgIGVsc2UgaWYgKEFycmF5LmlzQXJyYXkob2JqKSl7XG4gICAgICAgICAgICBsZW4gPSBvYmoubGVuZ3RoO1xuICAgICAgICAgICAgZm9yKGkgPSAwOyBpIDwgbGVuOyBpKyspe1xuICAgICAgICAgICAgICBtb3JlID0gc2NhbkZvclZhbHVlKG9ialtpXSwgdmFsLCBzYXZlUGF0aCwgcGF0aCA9PT0gJycgPyBpIDogcGF0aCArIHByb3BlcnR5U2VwYXJhdG9yICsgaSwgaXNDaXJjdWxhckNiKTtcbiAgICAgICAgICAgICAgICAvLyBDYWxsIGBzY2FuRm9yVmFsdWVgIHJlY3Vyc2l2ZWx5XG4gICAgICAgICAgICAgICAgLy8gSGFsdCBpZiB0aGF0IHJlY3Vyc2l2ZSBjYWxsIHJldHVybmVkIFwiZmFsc2VcIlxuICAgICAgICAgICAgICAgIGlmICghbW9yZSl7IHJldHVybjsgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHRydWU7IC8vIGtlZXAgbG9va2luZ1xuICAgICAgICB9XG4gICAgICAgIC8vIFRoaXMgb2JqZWN0IGlzIGFuIG9iamVjdCwgc28gZXhhbWluZSBlYWNoIGxvY2FsIHByb3BlcnR5IHNlcGFyYXRlbHlcbiAgICAgICAgZWxzZSBpZiAoaXNPYmplY3Qob2JqKSkge1xuICAgICAgICAgICAga2V5cyA9IE9iamVjdC5rZXlzKG9iaik7XG4gICAgICAgICAgICBsZW4gPSBrZXlzLmxlbmd0aDtcbiAgICAgICAgICAgIGlmIChsZW4gPiAxKXsga2V5cyA9IGtleXMuc29ydCgpOyB9IC8vIEZvcmNlIG9yZGVyIG9mIG9iamVjdCBrZXlzIHRvIHByb2R1Y2UgcmVwZWF0YWJsZSByZXN1bHRzXG4gICAgICAgICAgICBmb3IgKGkgPSAwOyBpIDwgbGVuOyBpKyspe1xuICAgICAgICAgICAgICAgIGlmIChvYmouaGFzT3duUHJvcGVydHkoa2V5c1tpXSkpe1xuICAgICAgICAgICAgICAgICAgICBwcm9wID0ga2V5c1tpXTtcbiAgICAgICAgICAgICAgICAgICAgLy8gUHJvcGVydHkgbWF5IGluY2x1ZGUgdGhlIHNlcGFyYXRvciBjaGFyYWN0ZXIgb3Igc29tZSBvdGhlciBzcGVjaWFsIGNoYXJhY3RlcixcbiAgICAgICAgICAgICAgICAgICAgLy8gc28gcXVvdGUgdGhpcyBwYXRoIHNlZ21lbnQgYW5kIGVzY2FwZSBhbnkgc2VwYXJhdG9ycyB3aXRoaW4uXG4gICAgICAgICAgICAgICAgICAgIGlmIChhbGxTcGVjaWFsc1JlZ0V4LnRlc3QocHJvcCkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgcHJvcCA9IHF1b3RlU3RyaW5nKHNpbmdsZXF1b3RlLCBwcm9wKTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICBtb3JlID0gc2NhbkZvclZhbHVlKG9ialtrZXlzW2ldXSwgdmFsLCBzYXZlUGF0aCwgcGF0aCA9PT0gJycgPyBwcm9wIDogcGF0aCArIHByb3BlcnR5U2VwYXJhdG9yICsgcHJvcCwgaXNDaXJjdWxhckNiKTtcbiAgICAgICAgICAgICAgICAgICAgaWYgKCFtb3JlKXsgcmV0dXJuOyB9XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHRydWU7IC8vIGtlZXAgbG9va2luZ1xuICAgICAgICB9XG4gICAgICAgIC8vIExlYWYgbm9kZSAoc3RyaW5nLCBudW1iZXIsIGNoYXJhY3RlciwgYm9vbGVhbiwgZXRjLiksIGJ1dCBkaWRuJ3QgbWF0Y2hcbiAgICAgICAgcmV0dXJuIHRydWU7IC8vIGtlZXAgbG9va2luZ1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBDaGVjayBpZiB0cnlpbmcgdG8gc2V0IG1hZ2ljIGF0dHJpYnV0ZXMuXG4gICAgICogQHByaXZhdGVcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30ga2V5IFxuICAgICAqIEByZXR1cm4ge0Jvb2xlYW59XG4gICAgICovXG4gICAgdmFyIGlzUHJvdG90eXBlUG9sbHV0ZWQgPSBmdW5jdGlvbihrZXkpIHtcbiAgICAgICAgcmV0dXJuIFsnX19wcm90b19fJywgJ2NvbnN0cnVjdG9yJywgJ3Byb3RvdHlwZSddLmluY2x1ZGVzKGtleSlcbiAgICB9XG5cbiAgICAvKipcbiAgICAgKiBHZXQgdG9rZW5pemVkIHJlcHJlc2VudGF0aW9uIG9mIHN0cmluZyBrZXlwYXRoLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gcGF0aCBLZXlwYXRoXG4gICAgICogQHJldHVybiB7T2JqZWN0fSBPYmplY3QgaW5jbHVkaW5nIHRoZSBhcnJheSBvZiBwYXRoIHRva2VucyBhbmQgYSBib29sZWFuIGluZGljYXRpbmcgXCJzaW1wbGVcIi4gU2ltcGxlIHRva2VuIHNldHMgaGF2ZSBubyBzcGVjaWFsIG9wZXJhdG9ycyBvciBuZXN0ZWQgdG9rZW5zLCBvbmx5IGEgcGxhaW4gYXJyYXkgb2Ygc3RyaW5ncyBmb3IgZmFzdCBldmFsdWF0aW9uLlxuICAgICAqL1xuICAgIF90aGlzLmdldFRva2VucyA9IGZ1bmN0aW9uKHBhdGgpe1xuICAgICAgICB2YXIgdG9rZW5zID0gdG9rZW5pemUocGF0aCk7XG4gICAgICAgIGlmICh0eXBlb2YgdG9rZW5zID09PSAkVU5ERUZJTkVEKXsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICByZXR1cm4gdG9rZW5zO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBJbmZvcm1zIHdoZXRoZXIgdGhlIHN0cmluZyBwYXRoIGhhcyB2YWxpZCBzeW50YXguIFRoZSBwYXRoIGlzIE5PVCBldmFsdWF0ZWQgYWdhaW5zdCBhXG4gICAgICogZGF0YSBvYmplY3QsIG9ubHkgdGhlIHN5bnRheCBpcyBjaGVja2VkLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gcGF0aCBLZXlwYXRoXG4gICAgICogQHJldHVybiB7Qm9vbGVhbn0gdmFsaWQgc3ludGF4IC0+IFwidHJ1ZVwiOyBub3QgdmFsaWQgLT4gXCJmYWxzZVwiXG4gICAgICovXG4gICAgX3RoaXMuaXNWYWxpZCA9IGZ1bmN0aW9uKHBhdGgpe1xuICAgICAgICByZXR1cm4gdHlwZW9mIHRva2VuaXplKHBhdGgpICE9PSAkVU5ERUZJTkVEO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBFc2NhcGVzIGFueSBzcGVjaWFsIGNoYXJhY3RlcnMgZm91bmQgaW4gdGhlIGlucHV0IHN0cmluZyB1c2luZyBiYWNrc2xhc2gsIHByZXZlbnRpbmdcbiAgICAgKiB0aGVzZSBjaGFyYWN0ZXJzIGZyb20gY2F1c2luZyB1bmludGVuZGVkIHByb2Nlc3NpbmcgYnkgUGF0aFRvb2xraXQuIFRoaXMgZnVuY3Rpb25cbiAgICAgKiBET0VTIHJlc3BlY3QgdGhlIGN1cnJlbnQgY29uZmlndXJlZCBzeW50YXgsIGV2ZW4gaWYgaXQgaGFzIGJlZW4gYWx0ZXJlZCBmcm9tIHRoZSBkZWZhdWx0LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gc2VnbWVudCBTZWdtZW50IG9mIGEga2V5cGF0aFxuICAgICAqIEByZXR1cm4ge1N0cmluZ30gVGhlIG9yaWdpbmFsIHNlZ21lbnQgc3RyaW5nIHdpdGggYWxsIFBhdGhUb29sa2l0IHNwZWNpYWwgY2hhcmFjdGVycyBwcmVwZW5kZWQgd2l0aCBcIlxcXCJcbiAgICAgKi9cbiAgICBfdGhpcy5lc2NhcGUgPSBmdW5jdGlvbihzZWdtZW50KXtcbiAgICAgICAgcmV0dXJuIHNlZ21lbnQucmVwbGFjZShhbGxTcGVjaWFsc1JlZ0V4LCAnXFxcXCQmJyk7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIEV2YWx1YXRlcyBrZXlwYXRoIGluIG9iamVjdCBhbmQgcmV0dXJucyB0aGUgdmFsdWUgZm91bmQgdGhlcmUsIGlmIGF2YWlsYWJsZS4gSWYgdGhlIHBhdGhcbiAgICAgKiBkb2VzIG5vdCBleGlzdCBpbiB0aGUgcHJvdmlkZWQgZGF0YSBvYmplY3QsIHJldHVybnMgYHVuZGVmaW5lZGAgKHRoaXMgcmV0dXJuIHZhbHVlIGlzXG4gICAgICogY29uZmlndXJhYmxlIGluIG9wdGlvbnMsIHNlZSBgc2V0RGVmYXVsdFJldHVyblZhbGAgYmVsb3cpLiBGb3IgXCJzaW1wbGVcIiBwYXRocywgd2hpY2hcbiAgICAgKiBkb24ndCBpbmNsdWRlIGFueSBvcGVyYXRpb25zIGJleW9uZCBwcm9wZXJ0eSBzZXBhcmF0b3JzLCBvcHRpbWl6ZWQgcmVzb2x2ZXJzIHdpbGwgYmUgdXNlZFxuICAgICAqIHdoaWNoIGFyZSBtb3JlIGxpZ2h0d2VpZ2h0IHRoYW4gdGhlIGZ1bGwtZmVhdHVyZWQgYHJlc29sdmVQYXRoYC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtBbnl9IG9iaiBTb3VyY2UgZGF0YSBvYmplY3RcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gcGF0aCBLZXlwYXRoIHRvIGV2YWx1YXRlIHdpdGhpbiBcIm9ialwiLiBBbHNvIGFjY2VwdHMgdG9rZW4gYXJyYXkgaW4gcGxhY2Ugb2YgYSBzdHJpbmcgcGF0aC5cbiAgICAgKiBAcmV0dXJuIHtBbnl9IElmIHRoZSBrZXlwYXRoIGV4aXN0cyBpbiBcIm9ialwiLCByZXR1cm4gdGhlIHZhbHVlIGF0IHRoYXQgbG9jYXRpb247IElmIG5vdCwgcmV0dXJuIGB1bmRlZmluZWRgLlxuICAgICAqL1xuICAgIF90aGlzLmdldCA9IGZ1bmN0aW9uIChvYmosIHBhdGgpe1xuICAgICAgICB2YXIgaSA9IDAsXG4gICAgICAgICAgICByZXR1cm5WYWwsXG4gICAgICAgICAgICBsZW4gPSBhcmd1bWVudHMubGVuZ3RoLFxuICAgICAgICAgICAgYXJncztcbiAgICAgICAgLy8gRm9yIHN0cmluZyBwYXRocywgZmlyc3Qgc2VlIGlmIHBhdGggaGFzIGFscmVhZHkgYmVlbiBjYWNoZWQgYW5kIGlmIHRoZSB0b2tlbiBzZXQgaXMgc2ltcGxlLiBJZlxuICAgICAgICAvLyBzbywgd2UgY2FuIHVzZSB0aGUgb3B0aW1pemVkIHRva2VuIGFycmF5IHJlc29sdmVyIHVzaW5nIHRoZSBjYWNoZWQgdG9rZW4gc2V0LlxuICAgICAgICAvLyBJZiB0aGVyZSBpcyBubyBjYWNoZWQgZW50cnksIHVzZSBSZWdFeCB0byBsb29rIGZvciBzcGVjaWFsIGNoYXJhY3RlcnMgYXBhcnQgZnJvbSB0aGUgc2VwYXJhdG9yLlxuICAgICAgICAvLyBJZiBub25lIGFyZSBmb3VuZCwgd2UgY2FuIHVzZSB0aGUgb3B0aW1pemVkIHN0cmluZyByZXNvbHZlci5cbiAgICAgICAgaWYgKHR5cGVvZiBwYXRoID09PSAkU1RSSU5HKXtcbiAgICAgICAgICAgIGlmIChvcHQudXNlQ2FjaGUgJiYgY2FjaGVbcGF0aF0gJiYgY2FjaGVbcGF0aF0uc2ltcGxlKXtcbiAgICAgICAgICAgICAgICByZXR1cm5WYWwgPSBxdWlja1Jlc29sdmVUb2tlbkFycmF5KG9iaiwgY2FjaGVbcGF0aF0udCk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIGlmICghc2ltcGxlUGF0aFJlZ0V4LnRlc3QocGF0aCkpe1xuICAgICAgICAgICAgICAgIHJldHVyblZhbCA9IHF1aWNrUmVzb2x2ZVN0cmluZyhvYmosIHBhdGgpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgLy8gSWYgd2UgbWFkZSBpdCB0aGlzIGZhciwgdGhlIHBhdGggaXMgY29tcGxleCBhbmQgbWF5IGluY2x1ZGUgcGxhY2Vob2xkZXJzLiBHYXRoZXIgdXAgYW55XG4gICAgICAgICAgICAvLyBleHRyYSBhcmd1bWVudHMgYW5kIGNhbGwgdGhlIGZ1bGwgYHJlc29sdmVQYXRoYCBmdW5jdGlvbi5cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIGFyZ3MgPSBbXTtcbiAgICAgICAgICAgICAgICBpZiAobGVuID4gMil7XG4gICAgICAgICAgICAgICAgICAgIGZvciAoaSA9IDI7IGkgPCBsZW47IGkrKykgeyBhcmdzW2ktMl0gPSBhcmd1bWVudHNbaV07IH1cbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgcmV0dXJuVmFsID0gcmVzb2x2ZVBhdGgob2JqLCBwYXRoLCB1bmRlZmluZWQsIGFyZ3MpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIC8vIEZvciBhcnJheSBwYXRocyAocHJlLWNvbXBpbGVkIHRva2VuIHNldHMpLCBjaGVjayBmb3Igc2ltcGxpY2l0eSBzbyB3ZSBjYW4gdXNlIHRoZSBvcHRpbWl6ZWQgcmVzb2x2ZXIuXG4gICAgICAgIGVsc2UgaWYgKEFycmF5LmlzQXJyYXkocGF0aC50KSAmJiBwYXRoLnNpbXBsZSl7XG4gICAgICAgICAgICByZXR1cm5WYWwgPSBxdWlja1Jlc29sdmVUb2tlbkFycmF5KG9iaiwgcGF0aC50KTtcbiAgICAgICAgfVxuICAgICAgICAvLyBJZiB3ZSBtYWRlIGl0IHRoaXMgZmFyLCB0aGUgcGF0aCBpcyBjb21wbGV4IGFuZCBtYXkgaW5jbHVkZSBwbGFjZWhvbGRlcnMuIEdhdGhlciB1cCBhbnlcbiAgICAgICAgLy8gZXh0cmEgYXJndW1lbnRzIGFuZCBjYWxsIHRoZSBmdWxsIGByZXNvbHZlUGF0aGAgZnVuY3Rpb24uXG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgYXJncyA9IFtdO1xuICAgICAgICAgICAgaWYgKGxlbiA+IDIpe1xuICAgICAgICAgICAgICAgIGZvciAoaSA9IDI7IGkgPCBsZW47IGkrKykgeyBhcmdzW2ktMl0gPSBhcmd1bWVudHNbaV07IH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVyblZhbCA9IHJlc29sdmVQYXRoKG9iaiwgcGF0aCwgdW5kZWZpbmVkLCBhcmdzKTtcbiAgICAgICAgfVxuXG4gICAgICAgIHJldHVybiByZXR1cm5WYWwgPT09IFVOREVGID8gb3B0LmRlZmF1bHRSZXR1cm5WYWwgOiByZXR1cm5WYWw7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIEV2YWx1YXRlcyBrZXlwYXRoIGluIG9iamVjdCBhbmQgcmV0dXJucyB0aGUgdmFsdWUgZm91bmQgdGhlcmUsIGlmIGF2YWlsYWJsZS4gSWYgdGhlIHBhdGhcbiAgICAgKiBkb2VzIG5vdCBleGlzdCBpbiB0aGUgcHJvdmlkZWQgZGF0YSBvYmplY3QsIHJldHVybnMgZGVmYXVsdCB2YWx1ZSBhcyBwcm92aWRlZCBpbiBhcmd1bWVudHMuXG4gICAgICogRm9yIFwic2ltcGxlXCIgcGF0aHMsIHdoaWNoIGRvbid0IGluY2x1ZGUgYW55IG9wZXJhdGlvbnMgYmV5b25kIHByb3BlcnR5IHNlcGFyYXRvcnMsIG9wdGltaXplZFxuICAgICAqIHJlc29sdmVycyB3aWxsIGJlIHVzZWQgd2hpY2ggYXJlIG1vcmUgbGlnaHR3ZWlnaHQgdGhhbiB0aGUgZnVsbC1mZWF0dXJlZCBgcmVzb2x2ZVBhdGhgLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge0FueX0gb2JqIFNvdXJjZSBkYXRhIG9iamVjdFxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBwYXRoIEtleXBhdGggdG8gZXZhbHVhdGUgd2l0aGluIFwib2JqXCIuIEFsc28gYWNjZXB0cyB0b2tlbiBhcnJheSBpbiBwbGFjZSBvZiBhIHN0cmluZyBwYXRoLlxuICAgICAqIEBwYXJhbSB7QW55fSBkZWZhdWx0UmV0dXJuVmFsIFZhbHVlIHRvIHJldHVybiBpZiBcImdldFwiIHJlc3VsdHMgaW4gdW5kZWZpbmVkLlxuICAgICAqIEByZXR1cm4ge0FueX0gSWYgdGhlIGtleXBhdGggZXhpc3RzIGluIFwib2JqXCIsIHJldHVybiB0aGUgdmFsdWUgYXQgdGhhdCBsb2NhdGlvbjsgSWYgbm90LCByZXR1cm4gdmFsdWUgZnJvbSBcImRlZmF1bHRSZXR1cm5WYWxcIi5cbiAgICAgKi9cbiAgICBfdGhpcy5nZXRXaXRoRGVmYXVsdCA9IGZ1bmN0aW9uIChvYmosIHBhdGgsIGRlZmF1bHRSZXR1cm5WYWwpe1xuICAgICAgICB2YXIgaSA9IDAsXG4gICAgICAgICAgICByZXR1cm5WYWwsXG4gICAgICAgICAgICBsZW4gPSBhcmd1bWVudHMubGVuZ3RoLFxuICAgICAgICAgICAgYXJncyA9IFsgb2JqLCBwYXRoIF07XG5cbiAgICAgICAgLy8gQ29kZSBiZWxvdyBkdXBsaWNhdGVzIFwiZ2V0XCIgbWV0aG9kIGFib3ZlIHJhdGhlciB0aGFuIHNpbXBseSBleGVjdXRpbmcgXCJnZXRcIiBhbmQgY3VzdG9taXppbmdcbiAgICAgICAgLy8gdGhlIHJldHVybiB2YWx1ZSBiZWNhdXNlIFwiZ2V0XCIgbWF5IGhhdmUgZmFpbGVkIHRvIHJlc29sdmUgYW5kIHJldHVybmVkIGEgbm9uLXVuZGVmaW5lZCB2YWx1ZVxuICAgICAgICAvLyBkdWUgdG8gYW4gaW5zdGFuY2Ugb3B0aW9uLCBvcHRpb25zLmRlZmF1bHRSZXR1cm5WYWwuIEluIHRoYXQgY2FzZSwgdGhpcyBtZXRob2QgY2FuJ3Qga25vd1xuICAgICAgICAvLyB3aGV0aGVyIHRoZSBub24tdW5kZWZpbmVkIHJldHVybiB2YWx1ZSB3YXMgdGhlIGFjdHVhbCB2YWx1ZSBhdCB0aGF0IHBhdGgsIG9yIHdhcyByZXR1cm5lZFxuICAgICAgICAvLyBkdWUgdG8gcGF0aCByZXNvbHV0aW9uIGZhaWx1cmUuIFRvIGJlIHNhZmUsIHRoZXJlZm9yZSwgdGhlIFwiZ2V0XCIgbG9naWMgaXMgZHVwbGljYXRlZCBidXRcbiAgICAgICAgLy8gdGhlIGRlZmF1bHRSZXR1cm5WYWwgYXJndW1lbnQgaXMgdXNlZCBpbiBwbGFjZSBvZiB0aGUgaW5zdGFuY2Ugb3B0aW9uIGluIGNhc2Ugb2YgZmFpbHVyZS5cblxuICAgICAgICAvLyBGb3Igc3RyaW5nIHBhdGhzLCBmaXJzdCBzZWUgaWYgcGF0aCBoYXMgYWxyZWFkeSBiZWVuIGNhY2hlZCBhbmQgaWYgdGhlIHRva2VuIHNldCBpcyBzaW1wbGUuIElmXG4gICAgICAgIC8vIHNvLCB3ZSBjYW4gdXNlIHRoZSBvcHRpbWl6ZWQgdG9rZW4gYXJyYXkgcmVzb2x2ZXIgdXNpbmcgdGhlIGNhY2hlZCB0b2tlbiBzZXQuXG4gICAgICAgIC8vIElmIHRoZXJlIGlzIG5vIGNhY2hlZCBlbnRyeSwgdXNlIFJlZ0V4IHRvIGxvb2sgZm9yIHNwZWNpYWwgY2hhcmFjdGVycyBhcGFydCBmcm9tIHRoZSBzZXBhcmF0b3IuXG4gICAgICAgIC8vIElmIG5vbmUgYXJlIGZvdW5kLCB3ZSBjYW4gdXNlIHRoZSBvcHRpbWl6ZWQgc3RyaW5nIHJlc29sdmVyLlxuICAgICAgICBpZiAodHlwZW9mIHBhdGggPT09ICRTVFJJTkcpe1xuICAgICAgICAgICAgaWYgKG9wdC51c2VDYWNoZSAmJiBjYWNoZVtwYXRoXSAmJiBjYWNoZVtwYXRoXS5zaW1wbGUpe1xuICAgICAgICAgICAgICAgIHJldHVyblZhbCA9IHF1aWNrUmVzb2x2ZVRva2VuQXJyYXkob2JqLCBjYWNoZVtwYXRoXS50KTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2UgaWYgKCFzaW1wbGVQYXRoUmVnRXgudGVzdChwYXRoKSl7XG4gICAgICAgICAgICAgICAgcmV0dXJuVmFsID0gcXVpY2tSZXNvbHZlU3RyaW5nKG9iaiwgcGF0aCk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICAvLyBJZiB3ZSBtYWRlIGl0IHRoaXMgZmFyLCB0aGUgcGF0aCBpcyBjb21wbGV4IGFuZCBtYXkgaW5jbHVkZSBwbGFjZWhvbGRlcnMuIEdhdGhlciB1cCBhbnlcbiAgICAgICAgICAgIC8vIGV4dHJhIGFyZ3VtZW50cyBhbmQgY2FsbCB0aGUgZnVsbCBgcmVzb2x2ZVBhdGhgIGZ1bmN0aW9uLlxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgYXJncyA9IFtdO1xuICAgICAgICAgICAgICAgIGlmIChsZW4gPiAzKXtcbiAgICAgICAgICAgICAgICAgICAgZm9yIChpID0gMzsgaSA8IGxlbjsgaSsrKSB7IGFyZ3NbaS0zXSA9IGFyZ3VtZW50c1tpXTsgfVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICByZXR1cm5WYWwgPSByZXNvbHZlUGF0aChvYmosIHBhdGgsIHVuZGVmaW5lZCwgYXJncyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgLy8gRm9yIGFycmF5IHBhdGhzIChwcmUtY29tcGlsZWQgdG9rZW4gc2V0cyksIGNoZWNrIGZvciBzaW1wbGljaXR5IHNvIHdlIGNhbiB1c2UgdGhlIG9wdGltaXplZCByZXNvbHZlci5cbiAgICAgICAgZWxzZSBpZiAoQXJyYXkuaXNBcnJheShwYXRoLnQpICYmIHBhdGguc2ltcGxlKXtcbiAgICAgICAgICAgIHJldHVyblZhbCA9IHF1aWNrUmVzb2x2ZVRva2VuQXJyYXkob2JqLCBwYXRoLnQpO1xuICAgICAgICB9XG4gICAgICAgIC8vIElmIHdlIG1hZGUgaXQgdGhpcyBmYXIsIHRoZSBwYXRoIGlzIGNvbXBsZXggYW5kIG1heSBpbmNsdWRlIHBsYWNlaG9sZGVycy4gR2F0aGVyIHVwIGFueVxuICAgICAgICAvLyBleHRyYSBhcmd1bWVudHMgYW5kIGNhbGwgdGhlIGZ1bGwgYHJlc29sdmVQYXRoYCBmdW5jdGlvbi5cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICBhcmdzID0gW107XG4gICAgICAgICAgICBpZiAobGVuID4gMyl7XG4gICAgICAgICAgICAgICAgZm9yIChpID0gMzsgaSA8IGxlbjsgaSsrKSB7IGFyZ3NbaS0zXSA9IGFyZ3VtZW50c1tpXTsgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuVmFsID0gcmVzb2x2ZVBhdGgob2JqLCBwYXRoLCB1bmRlZmluZWQsIGFyZ3MpO1xuICAgICAgICB9XG5cbiAgICAgICAgcmV0dXJuIHJldHVyblZhbCA9PT0gVU5ERUYgPyBkZWZhdWx0UmV0dXJuVmFsIDogcmV0dXJuVmFsO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBFdmFsdWF0ZXMgYSBrZXlwYXRoIGluIG9iamVjdCBhbmQgc2V0cyBhIG5ldyB2YWx1ZSBhdCB0aGUgcG9pbnQgZGVzY3JpYmVkIGluIHRoZSBrZXlwYXRoLiBJZlxuICAgICAqIFwiZm9yY2VcIiBpcyBkaXNhYmxlZCwgdGhlIGZ1bGwgcGF0aCBtdXN0IGV4aXN0IHVwIHRvIHRoZSBmaW5hbCBwcm9wZXJ0eSwgd2hpY2ggbWF5IGJlIGNyZWF0ZWRcbiAgICAgKiBieSB0aGUgc2V0IG9wZXJhdGlvbi4gSWYgXCJmb3JjZVwiIGlzIGVuYWJsZWQsIGFueSBtaXNzaW5nIGludGVybWVkaWF0ZSBwcm9wZXJ0aWVzIHdpbGwgYmUgY3JlYXRlZFxuICAgICAqIGluIG9yZGVyIHRvIHNldCB0aGUgdmFsdWUgb24gdGhlIGZpbmFsIHByb3BlcnR5LiBJZiBgc2V0YCBzdWNjZWVkcywgcmV0dXJucyBcInRydWVcIiwgb3RoZXJ3aXNlIFwiZmFsc2VcIi5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtBbnl9IG9iaiBTb3VyY2UgZGF0YSBvYmplY3RcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gcGF0aCBLZXlwYXRoIHRvIGV2YWx1YXRlIHdpdGhpbiBcIm9ialwiLiBBbHNvIGFjY2VwdHMgdG9rZW4gYXJyYXkgaW4gcGxhY2Ugb2YgYSBzdHJpbmcgcGF0aC5cbiAgICAgKiBAcGFyYW0ge0FueX0gdmFsIE5ldyB2YWx1ZSB0byBzZXQgYXQgdGhlIGxvY2F0aW9uIGRlc2NyaWJlZCBpbiBcInBhdGhcIlxuICAgICAqIEByZXR1cm4ge0Jvb2xlYW59IFwidHJ1ZVwiIGlmIHRoZSBzZXQgb3BlcmF0aW9uIHN1Y2NlZWRzOyBcImZhbHNlXCIgaWYgaXQgZG9lcyBub3Qgc3VjY2VlZFxuICAgICAqL1xuICAgIF90aGlzLnNldCA9IGZ1bmN0aW9uKG9iaiwgcGF0aCwgdmFsKXtcbiAgICAgICAgdmFyIGkgPSAwLFxuICAgICAgICAgICAgbGVuID0gYXJndW1lbnRzLmxlbmd0aCxcbiAgICAgICAgICAgIGFyZ3MsXG4gICAgICAgICAgICByZWYsXG4gICAgICAgICAgICBkb25lID0gZmFsc2U7XG5cbiAgICAgICAgLy8gUGF0aCByZXNvbHV0aW9uIGZvbGxvd3MgdGhlIHNhbWUgbG9naWMgYXMgYGdldGAgYWJvdmUsIHdpdGggb25lIGRpZmZlcmVuY2U6IGBnZXRgIHdpbGxcbiAgICAgICAgLy8gYWJvcnQgYnkgcmV0dXJuaW5nIHRoZSB2YWx1ZSBhcyBzb29uIGFzIGl0J3MgZm91bmQuIGBzZXRgIGRvZXMgbm90IGFib3J0IHNvIHRoZSBpZi1lbHNlXG4gICAgICAgIC8vIHN0cnVjdHVyZSBpcyBzbGlnaHRseSBkaWZmZXJlbnQgdG8gZGljdGF0ZSB3aGVuL2lmIHRoZSBmaW5hbCBjYXNlIHNob3VsZCBleGVjdXRlLlxuICAgICAgICBpZiAodHlwZW9mIHBhdGggPT09ICRTVFJJTkcpe1xuICAgICAgICAgICAgaWYgKG9wdC51c2VDYWNoZSAmJiBjYWNoZVtwYXRoXSAmJiBjYWNoZVtwYXRoXS5zaW1wbGUpe1xuICAgICAgICAgICAgICAgIHJlZiA9IHF1aWNrUmVzb2x2ZVRva2VuQXJyYXkob2JqLCBjYWNoZVtwYXRoXS50LCB2YWwpO1xuICAgICAgICAgICAgICAgIGRvbmUgfD0gdHJ1ZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2UgaWYgKCFzaW1wbGVQYXRoUmVnRXgudGVzdChwYXRoKSl7XG4gICAgICAgICAgICAgICAgcmVmID0gcXVpY2tSZXNvbHZlU3RyaW5nKG9iaiwgcGF0aCwgdmFsKTtcbiAgICAgICAgICAgICAgICBkb25lIHw9IHRydWU7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAoQXJyYXkuaXNBcnJheShwYXRoLnQpICYmIHBhdGguc2ltcGxlKXtcbiAgICAgICAgICAgIHJlZiA9IHF1aWNrUmVzb2x2ZVRva2VuQXJyYXkob2JqLCBwYXRoLnQsIHZhbCk7XG4gICAgICAgICAgICBkb25lIHw9IHRydWU7XG4gICAgICAgIH1cblxuICAgICAgICAvLyBQYXRoIHdhcyAocHJvYmFibHkpIGEgc3RyaW5nIGFuZCBpdCBjb250YWluZWQgY29tcGxleCBwYXRoIGNoYXJhY3RlcnNcbiAgICAgICAgaWYgKCFkb25lKSB7XG4gICAgICAgICAgICBpZiAobGVuID4gMyl7XG4gICAgICAgICAgICAgICAgYXJncyA9IFtdO1xuICAgICAgICAgICAgICAgIGZvciAoaSA9IDM7IGkgPCBsZW47IGkrKykgeyBhcmdzW2ktM10gPSBhcmd1bWVudHNbaV07IH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJlZiA9IHJlc29sdmVQYXRoKG9iaiwgcGF0aCwgdmFsLCBhcmdzKTtcbiAgICAgICAgfVxuXG4gICAgICAgIC8vIGBzZXRgIGNhbiBzZXQgYSBuZXcgdmFsdWUgaW4gbXVsdGlwbGUgcGxhY2VzIGlmIHRoZSBmaW5hbCBwYXRoIHNlZ21lbnQgaXMgYW4gYXJyYXkuXG4gICAgICAgIC8vIElmIGFueSBvZiB0aG9zZSB2YWx1ZSBhc3NpZ25tZW50cyBmYWlsLCBgc2V0YCB3aWxsIHJldHVybiBcImZhbHNlXCIgaW5kaWNhdGluZyBmYWlsdXJlLlxuICAgICAgICBpZiAoQXJyYXkuaXNBcnJheShyZWYpKXtcbiAgICAgICAgICAgIHJldHVybiByZWYuaW5kZXhPZih1bmRlZmluZWQpID09PSAtMTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gcmVmICE9PSBVTkRFRjtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogTG9jYXRlIGEgdmFsdWUgd2l0aGluIGFuIG9iamVjdCBvciBhcnJheS4gVGhpcyBpcyB0aGUgcHVibGljbHkgZXhwb3NlZCBpbnRlcmZhY2UgdG8gdGhlXG4gICAgICogcHJpdmF0ZSBgc2NhbkZvclZhbHVlYCBmdW5jdGlvbiBkZWZpbmVkIGFib3ZlLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge0FueX0gb2JqIFNvdXJjZSBkYXRhIG9iamVjdFxuICAgICAqIEBwYXJhbSB7QW55fSB2YWwgVGhlIHZhbHVlIHRvIHNlYXJjaCBmb3Igd2l0aGluIFwib2JqXCJcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gb25lT3JNYW55IE9wdGlvbmFsOyBJZiBtaXNzaW5nIG9yIFwib25lXCIsIGBmaW5kYCB3aWxsIG9ubHkgcmV0dXJuIHRoZSBmaXJzdCB2YWxpZCBwYXRoLiBJZiBcIm9uT3JNYW55XCIgaXMgYW55IG90aGVyIHN0cmluZywgYGZpbmRgIHdpbGwgc2NhbiB0aGUgZnVsbCBvYmplY3QgbG9va2luZyBmb3IgYWxsIHZhbGlkIHBhdGhzIHRvIGFsbCBjYXNlcyB3aGVyZSBcInZhbFwiIGFwcGVhcnMuXG4gICAgICogQHJldHVybiB7QXJyYXl9IEFycmF5IG9mIGtleXBhdGhzIHRvIFwidmFsXCIgb3IgYHVuZGVmaW5lZGAgaWYgXCJ2YWxcIiBpcyBub3QgZm91bmQuXG4gICAgICovXG4gICAgX3RoaXMuZmluZCA9IGZ1bmN0aW9uKG9iaiwgdmFsLCBvbmVPck1hbnkpe1xuICAgICAgICB2YXIgZm91bmRQYXRocyA9IFtdO1xuICAgICAgICAvLyBzYXZlUGF0aCBpcyB0aGUgY2FsbGJhY2sgd2hpY2ggd2lsbCBhY2N1bXVsYXRlIGFueSBmb3VuZCBwYXRocyBpbiBhIGxvY2FsIGFycmF5XG4gICAgICAgIHZhciBzYXZlUGF0aCA9IGZ1bmN0aW9uKHBhdGgpe1xuICAgICAgICAgICAgZm91bmRQYXRocy5wdXNoKHBhdGgpO1xuICAgICAgICAgICAgaWYoIW9uZU9yTWFueSB8fCBvbmVPck1hbnkgPT09ICdvbmUnKXtcbiAgICAgICAgICAgICAgICByZXR1cm4gZmFsc2U7IC8vIHN0b3Agc2Nhbm5pbmcgZm9yIHZhbHVlXG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gdHJ1ZTsgLy8ga2VlcCBzY2FubmluZyBmb3IgdmFsdWUgZWxzZXdoZXJlIGluIG9iamVjdFxuICAgICAgICB9O1xuICAgICAgICBzY2FuRm9yVmFsdWUob2JqLCB2YWwsIHNhdmVQYXRoKTtcbiAgICAgICAgaWYoIW9uZU9yTWFueSB8fCBvbmVPck1hbnkgPT09ICdvbmUnKXtcbiAgICAgICAgICAgIHJldHVybiBmb3VuZFBhdGhzLmxlbmd0aCA+IDAgPyBmb3VuZFBhdGhzWzBdIDogdW5kZWZpbmVkO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBmb3VuZFBhdGhzLmxlbmd0aCA+IDAgPyBmb3VuZFBhdGhzIDogdW5kZWZpbmVkO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBMb2NhdGUgYSB2YWx1ZSB3aXRoaW4gYW4gb2JqZWN0IG9yIGFycmF5LiBEdXJpbmcgc2NhbiwgcHJvdGVjdCBhZ2FpbnN0IGxvb3AgcmVmZXJlbmNlcy5cbiAgICAgKiBUaGlzIGlzIHRoZSBwdWJsaWNseSBleHBvc2VkIGludGVyZmFjZSB0byB0aGUgcHJpdmF0ZSBgc2NhbkZvclZhbHVlYCBmdW5jdGlvbiBkZWZpbmVkIGFib3ZlLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge0FueX0gb2JqIFNvdXJjZSBkYXRhIG9iamVjdFxuICAgICAqIEBwYXJhbSB7QW55fSB2YWwgVGhlIHZhbHVlIHRvIHNlYXJjaCBmb3Igd2l0aGluIFwib2JqXCJcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gb25lT3JNYW55IE9wdGlvbmFsOyBJZiBtaXNzaW5nIG9yIFwib25lXCIsIGBmaW5kYCB3aWxsIG9ubHkgcmV0dXJuIHRoZSBmaXJzdCB2YWxpZCBwYXRoLiBJZiBcIm9uT3JNYW55XCIgaXMgYW55IG90aGVyIHN0cmluZywgYGZpbmRgIHdpbGwgc2NhbiB0aGUgZnVsbCBvYmplY3QgbG9va2luZyBmb3IgYWxsIHZhbGlkIHBhdGhzIHRvIGFsbCBjYXNlcyB3aGVyZSBcInZhbFwiIGFwcGVhcnMuXG4gICAgICogQHJldHVybiB7QXJyYXl9IEFycmF5IG9mIGtleXBhdGhzIHRvIFwidmFsXCIgb3IgYHVuZGVmaW5lZGAgaWYgXCJ2YWxcIiBpcyBub3QgZm91bmQuXG4gICAgICovXG4gICAgX3RoaXMuZmluZFNhZmUgPSBmdW5jdGlvbihvYmosIHZhbCwgb25lT3JNYW55KXtcbiAgICAgICAgdmFyIGZvdW5kUGF0aHMgPSBbXTtcbiAgICAgICAgLy8gc2F2ZVBhdGggaXMgdGhlIGNhbGxiYWNrIHdoaWNoIHdpbGwgYWNjdW11bGF0ZSBhbnkgZm91bmQgcGF0aHMgaW4gYSBsb2NhbCBhcnJheVxuICAgICAgICAvLyB2YXJpYWJsZS5cbiAgICAgICAgdmFyIHNhdmVQYXRoID0gZnVuY3Rpb24ocGF0aCl7XG4gICAgICAgICAgICBmb3VuZFBhdGhzLnB1c2gocGF0aCk7XG4gICAgICAgICAgICBpZighb25lT3JNYW55IHx8IG9uZU9yTWFueSA9PT0gJ29uZScpe1xuICAgICAgICAgICAgICAgIHJldHVybiBmYWxzZTsgLy8gc3RvcCBzY2FubmluZyBmb3IgdmFsdWVcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiB0cnVlOyAvLyBrZWVwIHNjYW5uaW5nIGZvciB2YWx1ZSBlbHNld2hlcmUgaW4gb2JqZWN0XG4gICAgICAgIH07XG4gICAgICAgIC8vIGlzQ2lyY3VsYXIgaXMgYSBjYWxsYmFjayB0aGF0IHdpbGwgdGVzdCBpZiB0aGlzIG9iamVjdCBhbHNvIGV4aXN0c1xuICAgICAgICAvLyBpbiBhbiBhbmNlc3RvciBwYXRoLCBpbmRpY2F0aW5nIGEgY2lyY3VsYXIgcmVmZXJlbmNlLlxuICAgICAgICB2YXIgaXNDaXJjdWxhciA9IGZ1bmN0aW9uKHJlZiwgcGF0aCl7XG4gICAgICAgICAgICB2YXIgdG9rZW5zID0gX3RoaXMuZ2V0VG9rZW5zKHBhdGgpO1xuICAgICAgICAgICAgLy8gV2FsayB1cCB0aGUgYW5jZXN0b3IgY2hhaW4gY2hlY2tpbmcgZm9yIGVxdWFsaXR5IHdpdGggY3VycmVudCBvYmplY3RcbiAgICAgICAgICAgIHdoaWxlKHRva2Vucy50LnBvcCgpKXtcbiAgICAgICAgICAgICAgICBpZihfdGhpcy5nZXQob2JqLCB0b2tlbnMpID09PSByZWYpe1xuICAgICAgICAgICAgICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgIH07XG4gICAgICAgIHNjYW5Gb3JWYWx1ZShvYmosIHZhbCwgc2F2ZVBhdGgsIFVOREVGLCBpc0NpcmN1bGFyKTtcbiAgICAgICAgaWYoIW9uZU9yTWFueSB8fCBvbmVPck1hbnkgPT09ICdvbmUnKXtcbiAgICAgICAgICAgIHJldHVybiBmb3VuZFBhdGhzLmxlbmd0aCA+IDAgPyBmb3VuZFBhdGhzWzBdIDogdW5kZWZpbmVkO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBmb3VuZFBhdGhzLmxlbmd0aCA+IDAgPyBmb3VuZFBhdGhzIDogdW5kZWZpbmVkO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBGb3IgYSBnaXZlbiBzcGVjaWFsIGNoYXJhY3RlciBncm91cCAoZS5nLiwgc2VwYXJhdG9ycykgYW5kIGNoYXJhY3RlciB0eXBlIChlLmcuLCBcInByb3BlcnR5XCIpLFxuICAgICAqIHJlcGxhY2UgYW4gZXhpc3Rpbmcgc2VwYXJhdG9yIHdpdGggYSBuZXcgY2hhcmFjdGVyLiBUaGlzIGNyZWF0ZXMgYSBuZXcgc3BlY2lhbCBjaGFyYWN0ZXIgZm9yXG4gICAgICogdGhhdCBwdXJwb3NlIGFud2l0aGluIHRoZSBjaGFyYWN0ZXIgZ3JvdXAgYW5kIHJlbW92ZXMgdGhlIG9sZCBvbmUuIEFsc28gdGFrZXMgYSBcImNsb3NlclwiIGFyZ3VtZW50XG4gICAgICogZm9yIGNhc2VzIHdoZXJlIHRoZSBzcGVjaWFsIGNoYXJhY3RlciBpcyBhIGNvbnRhaW5lciBzZXQuXG4gICAgICogQHByaXZhdGVcbiAgICAgKiBAcGFyYW0ge09iamVjdH0gb3B0aW9uR3JvdXAgUmVmZXJlbmNlIHRvIGN1cnJlbnQgY29uZmlndXJhdGlvbiBmb3IgYSBjZXJ0YWluIHR5cGUgb2Ygc3BlY2lhbCBjaGFyYWN0ZXJzXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IGNoYXJUeXBlIFRoZSB0eXBlIG9mIHNwZWNpYWwgY2hhcmFjdGVyIHRvIGJlIHJlcGxhY2VkXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHZhbCBOZXcgc3BlY2lhbCBjaGFyYWN0ZXIgc3RyaW5nXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IGNsb3NlciBPcHRpb25hbDsgTmV3IHNwZWNpYWwgY2hhcmFjdGVyIGNsb3NlciBzdHJpbmcsIG9ubHkgdXNlZCBmb3IgXCJjb250YWluZXJzXCIgZ3JvdXBcbiAgICAgKi9cbiAgICB2YXIgdXBkYXRlT3B0aW9uQ2hhciA9IGZ1bmN0aW9uKG9wdGlvbkdyb3VwLCBjaGFyVHlwZSwgdmFsLCBjbG9zZXIpe1xuICAgICAgICB2YXIgb2xkVmFsID0gJyc7XG4gICAgICAgIE9iamVjdC5rZXlzKG9wdGlvbkdyb3VwKS5mb3JFYWNoKGZ1bmN0aW9uKHN0cil7IGlmIChvcHRpb25Hcm91cFtzdHJdLmV4ZWMgPT09IGNoYXJUeXBlKXsgb2xkVmFsID0gc3RyOyB9IH0pO1xuXG4gICAgICAgIGRlbGV0ZSBvcHRpb25Hcm91cFtvbGRWYWxdO1xuICAgICAgICBvcHRpb25Hcm91cFt2YWxdID0ge2V4ZWM6IGNoYXJUeXBlfTtcbiAgICAgICAgaWYgKGNsb3Nlcil7IG9wdGlvbkdyb3VwW3ZhbF0uY2xvc2VyID0gY2xvc2VyOyB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIFNldHMgXCJzaW1wbGVcIiBzeW50YXggaW4gc3BlY2lhbCBjaGFyYWN0ZXIgZ3JvdXBzLiBUaGlzIHN5bnRheCBvbmx5IHN1cHBvcnRzIGEgc2VwYXJhdG9yXG4gICAgICogY2hhcmFjdGVyIGFuZCBubyBvdGhlciBvcGVyYXRvcnMuIEEgY3VzdG9tIHNlcGFyYXRvciBtYXkgYmUgcHJvdmlkZWQgYXMgYW4gYXJndW1lbnQuXG4gICAgICogQHByaXZhdGVcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gc2VwIE9wdGlvbmFsOyBTZXBhcmF0b3Igc3RyaW5nLiBJZiBtaXNzaW5nLCB0aGUgZGVmYXVsdCBzZXBhcmF0b3IgKFwiLlwiKSBpcyB1c2VkLlxuICAgICAqL1xuICAgIHZhciBzZXRTaW1wbGVPcHRpb25zID0gZnVuY3Rpb24oc2VwKXtcbiAgICAgICAgdmFyIHNlcE9wdHMgPSB7fTtcbiAgICAgICAgaWYgKCEodHlwZW9mIHNlcCA9PT0gJFNUUklORyAmJiBzZXAubGVuZ3RoID09PSAxKSl7XG4gICAgICAgICAgICBzZXAgPSAnLic7XG4gICAgICAgIH1cbiAgICAgICAgc2VwT3B0c1tzZXBdID0ge2V4ZWM6ICRQUk9QRVJUWX07XG4gICAgICAgIG9wdC5wcmVmaXhlcyA9IHt9O1xuICAgICAgICBvcHQuY29udGFpbmVycyA9IHt9O1xuICAgICAgICBvcHQuc2VwYXJhdG9ycyA9IHNlcE9wdHM7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIEFsdGVyIFBhdGhUb29sa2l0IGNvbmZpZ3VyYXRpb24uIFRha2VzIGFuIG9wdGlvbnMgaGFzaCB3aGljaCBtYXkgaW5jbHVkZVxuICAgICAqIG11bHRpcGxlIHNldHRpbmdzIHRvIGNoYW5nZSBhdCBvbmNlLiBJZiB0aGUgcGF0aCBzeW50YXggaXMgY2hhbmdlZCBieVxuICAgICAqIGNoYW5naW5nIHNwZWNpYWwgY2hhcmFjdGVycywgdGhlIGNhY2hlIGlzIHdpcGVkLiBFYWNoIG9wdGlvbiBncm91cCBpc1xuICAgICAqIFJFUExBQ0VEIGJ5IHRoZSBuZXcgb3B0aW9uIGdyb3VwIHBhc3NlZCBpbi4gSWYgYW4gb3B0aW9uIGdyb3VwIGlzIG5vdFxuICAgICAqIGluY2x1ZGVkIGluIHRoZSBvcHRpb25zIGhhc2gsIGl0IGlzIG5vdCBjaGFuZ2VkLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge09iamVjdH0gb3B0aW9ucyBPcHRpb24gaGFzaC4gRm9yIHNhbXBsZSBpbnB1dCwgc2VlIGBzZXREZWZhdWx0T3B0aW9uc2AgYWJvdmUuXG4gICAgICovXG4gICAgX3RoaXMuc2V0T3B0aW9ucyA9IGZ1bmN0aW9uKG9wdGlvbnMpe1xuICAgICAgICBpZiAob3B0aW9ucy5wcmVmaXhlcyl7XG4gICAgICAgICAgICBvcHQucHJlZml4ZXMgPSBvcHRpb25zLnByZWZpeGVzO1xuICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgfVxuICAgICAgICBpZiAob3B0aW9ucy5zZXBhcmF0b3JzKXtcbiAgICAgICAgICAgIG9wdC5zZXBhcmF0b3JzID0gb3B0aW9ucy5zZXBhcmF0b3JzO1xuICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgfVxuICAgICAgICBpZiAob3B0aW9ucy5jb250YWluZXJzKXtcbiAgICAgICAgICAgIG9wdC5jb250YWluZXJzID0gb3B0aW9ucy5jb250YWluZXJzO1xuICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgfVxuICAgICAgICBpZiAodHlwZW9mIG9wdGlvbnMuY2FjaGUgIT09ICRVTkRFRklORUQpe1xuICAgICAgICAgICAgb3B0LnVzZUNhY2hlID0gISFvcHRpb25zLmNhY2hlO1xuICAgICAgICB9XG4gICAgICAgIGlmICh0eXBlb2Ygb3B0aW9ucy5zaW1wbGUgIT09ICRVTkRFRklORUQpe1xuICAgICAgICAgICAgdmFyIHRlbXBDYWNoZSA9IG9wdC51c2VDYWNoZTsgLy8gcHJlc2VydmUgdGhlc2UgdHdvIG9wdGlvbnMgYWZ0ZXIgXCJzZXREZWZhdWx0T3B0aW9uc1wiXG4gICAgICAgICAgICB2YXIgdGVtcEZvcmNlID0gb3B0LmZvcmNlO1xuICAgICAgICAgICAgdmFyIHRlbXBEZWZhdWx0UmV0dXJuVmFsID0gb3B0LmRlZmF1bHRSZXR1cm5WYWw7XG5cbiAgICAgICAgICAgIG9wdC5zaW1wbGUgPSB0cnV0aGlmeShvcHRpb25zLnNpbXBsZSk7XG4gICAgICAgICAgICBpZiAob3B0LnNpbXBsZSl7XG4gICAgICAgICAgICAgICAgc2V0U2ltcGxlT3B0aW9ucygpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgc2V0RGVmYXVsdE9wdGlvbnMoKTtcbiAgICAgICAgICAgICAgICBvcHQudXNlQ2FjaGUgPSB0ZW1wQ2FjaGU7XG4gICAgICAgICAgICAgICAgb3B0LmZvcmNlID0gdGVtcEZvcmNlO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgfVxuICAgICAgICBpZiAodHlwZW9mIG9wdGlvbnMuZm9yY2UgIT09ICRVTkRFRklORUQpe1xuICAgICAgICAgICAgb3B0LmZvcmNlID0gdHJ1dGhpZnkob3B0aW9ucy5mb3JjZSk7XG4gICAgICAgIH1cbiAgICAgICAgLy8gVGhlIGRlZmF1bHQgcmV0dXJuIHZhbHVlIG1heSBiZSBzZXQgdG8gdW5kZWZpbmVkLCB3aGljaFxuICAgICAgICAvLyBtYWtlcyB0ZXN0aW5nIGZvciB0aGlzIG9wdGlvbiBtb3JlIHRyaWNreS5cbiAgICAgICAgaWYgKE9iamVjdC5rZXlzKG9wdGlvbnMpLmluY2x1ZGVzKCdkZWZhdWx0UmV0dXJuVmFsJykpe1xuICAgICAgICAgICAgb3B0WydkZWZhdWx0UmV0dXJuVmFsJ10gPSBvcHRpb25zLmRlZmF1bHRSZXR1cm5WYWw7XG4gICAgICAgIH1cbiAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogU2V0cyB1c2Ugb2Yga2V5cGF0aCBjYWNoZSB0byBlbmFibGVkIG9yIGRpc2FibGVkLCBkZXBlbmRpbmcgb24gaW5wdXQgdmFsdWUuXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7QW55fSB2YWwgVmFsdWUgd2hpY2ggd2lsbCBiZSBpbnRlcnByZXRlZCBhcyBhIGJvb2xlYW4gdXNpbmcgYHRydXRoaWZ5YC4gXCJ0cnVlXCIgd2lsbCBlbmFibGUgY2FjaGU7IFwiZmFsc2VcIiB3aWxsIGRpc2FibGUuXG4gICAgICovXG4gICAgX3RoaXMuc2V0Q2FjaGUgPSBmdW5jdGlvbih2YWwpe1xuICAgICAgICBvcHQudXNlQ2FjaGUgPSB0cnV0aGlmeSh2YWwpO1xuICAgIH07XG4gICAgLyoqXG4gICAgICogRW5hYmxlcyB1c2Ugb2Yga2V5cGF0aCBjYWNoZS5cbiAgICAgKiBAcHVibGljXG4gICAgICovXG4gICAgX3RoaXMuc2V0Q2FjaGVPbiA9IGZ1bmN0aW9uKCl7XG4gICAgICAgIG9wdC51c2VDYWNoZSA9IHRydWU7XG4gICAgfTtcbiAgICAvKipcbiAgICAgKiBEaXNhYmxlcyB1c2Ugb2Yga2V5cGF0aCBjYWNoZS5cbiAgICAgKiBAcHVibGljXG4gICAgICovXG4gICAgX3RoaXMuc2V0Q2FjaGVPZmYgPSBmdW5jdGlvbigpe1xuICAgICAgICBvcHQudXNlQ2FjaGUgPSBmYWxzZTtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogU2V0cyBcImZvcmNlXCIgb3B0aW9uIHdoZW4gc2V0dGluZyB2YWx1ZXMgaW4gYW4gb2JqZWN0LCBkZXBlbmRpbmcgb24gaW5wdXQgdmFsdWUuXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7QW55fSB2YWwgVmFsdWUgd2hpY2ggd2lsbCBiZSBpbnRlcnByZXRlZCBhcyBhIGJvb2xlYW4gdXNpbmcgYHRydXRoaWZ5YC4gXCJ0cnVlXCIgZW5hYmxlcyBcImZvcmNlXCI7IFwiZmFsc2VcIiBkaXNhYmxlcy5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRGb3JjZSA9IGZ1bmN0aW9uKHZhbCl7XG4gICAgICAgIG9wdC5mb3JjZSA9IHRydXRoaWZ5KHZhbCk7XG4gICAgfTtcbiAgICAvKipcbiAgICAgKiBFbmFibGVzIFwiZm9yY2VcIiBvcHRpb24gd2hlbiBzZXR0aW5nIHZhbHVlcyBpbiBhbiBvYmplY3QuXG4gICAgICogQHB1YmxpY1xuICAgICAqL1xuICAgIF90aGlzLnNldEZvcmNlT24gPSBmdW5jdGlvbigpe1xuICAgICAgICBvcHQuZm9yY2UgPSB0cnVlO1xuICAgIH07XG4gICAgLyoqXG4gICAgICogRGlzYWJsZXMgXCJmb3JjZVwiIG9wdGlvbiB3aGVuIHNldHRpbmcgdmFsdWVzIGluIGFuIG9iamVjdC5cbiAgICAgKiBAcHVibGljXG4gICAgICovXG4gICAgX3RoaXMuc2V0Rm9yY2VPZmYgPSBmdW5jdGlvbigpe1xuICAgICAgICBvcHQuZm9yY2UgPSBmYWxzZTtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogU2hvcnRjdXQgZnVuY3Rpb24gdG8gYWx0ZXIgUGF0aFRvb2xraXQgc3ludGF4IHRvIGEgXCJzaW1wbGVcIiBtb2RlIHRoYXQgb25seSB1c2VzXG4gICAgICogc2VwYXJhdG9ycyBhbmQgbm8gb3RoZXIgb3BlcmF0b3JzLiBcIlNpbXBsZVwiIG1vZGUgaXMgZW5hYmxlZCBvciBkaXNhYmxlZCBhY2NvcmRpbmdcbiAgICAgKiB0byB0aGUgZmlyc3QgYXJndW1lbnQgYW5kIHRoZSBzZXBhcmF0b3IgbWF5IGJlIGN1c3RvbWl6ZWQgd2l0aCB0aGUgc2Vjb25kXG4gICAgICogYXJndW1lbnQgd2hlbiBlbmFibGluZyBcInNpbXBsZVwiIG1vZGUuXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7QW55fSB2YWwgVmFsdWUgd2hpY2ggd2lsbCBiZSBpbnRlcnByZXRlZCBhcyBhIGJvb2xlYW4gdXNpbmcgYHRydXRoaWZ5YC4gXCJ0cnVlXCIgZW5hYmxlcyBcInNpbXBsZVwiIG1vZGU7IFwiZmFsc2VcIiBkaXNhYmxlcy5cbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gc2VwIFNlcGFyYXRvciBzdHJpbmcgdG8gdXNlIGluIHBsYWNlIG9mIHRoZSBkZWZhdWx0IFwiLlwiXG4gICAgICovXG4gICAgX3RoaXMuc2V0U2ltcGxlID0gZnVuY3Rpb24odmFsLCBzZXApe1xuICAgICAgICB2YXIgdGVtcENhY2hlID0gb3B0LnVzZUNhY2hlOyAvLyBwcmVzZXJ2ZSB0aGVzZSB0d28gb3B0aW9ucyBhZnRlciBcInNldERlZmF1bHRPcHRpb25zXCJcbiAgICAgICAgdmFyIHRlbXBGb3JjZSA9IG9wdC5mb3JjZTtcbiAgICAgICAgb3B0LnNpbXBsZSA9IHRydXRoaWZ5KHZhbCk7XG4gICAgICAgIGlmIChvcHQuc2ltcGxlKXtcbiAgICAgICAgICAgIHNldFNpbXBsZU9wdGlvbnMoc2VwKTtcbiAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICBzZXREZWZhdWx0T3B0aW9ucygpO1xuICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgICAgIG9wdC51c2VDYWNoZSA9IHRlbXBDYWNoZTtcbiAgICAgICAgICAgIG9wdC5mb3JjZSA9IHRlbXBGb3JjZTtcbiAgICAgICAgfVxuICAgICAgICBjYWNoZSA9IHt9O1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBFbmFibGVzIFwic2ltcGxlXCIgbW9kZVxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gc2VwIFNlcGFyYXRvciBzdHJpbmcgdG8gdXNlIGluIHBsYWNlIG9mIHRoZSBkZWZhdWx0IFwiLlwiXG4gICAgICogQHNlZSBzZXRTaW1wbGVcbiAgICAgKi9cbiAgICBfdGhpcy5zZXRTaW1wbGVPbiA9IGZ1bmN0aW9uKHNlcCl7XG4gICAgICAgIG9wdC5zaW1wbGUgPSB0cnVlO1xuICAgICAgICBzZXRTaW1wbGVPcHRpb25zKHNlcCk7XG4gICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgIGNhY2hlID0ge307XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIERpc2FibGVzIFwic2ltcGxlXCIgbW9kZSwgcmVzdG9yZXMgZGVmYXVsdCBQYXRoVG9vbGtpdCBzeW50YXhcbiAgICAgKiBAcHVibGljXG4gICAgICogQHNlZSBzZXRTaW1wbGVcbiAgICAgKiBAc2VlIHNldERlZmF1bHRPcHRpb25zXG4gICAgICovXG4gICAgX3RoaXMuc2V0U2ltcGxlT2ZmID0gZnVuY3Rpb24oKXtcbiAgICAgICAgdmFyIHRlbXBDYWNoZSA9IG9wdC51c2VDYWNoZTsgLy8gcHJlc2VydmUgdGhlc2UgdHdvIG9wdGlvbnMgYWZ0ZXIgXCJzZXREZWZhdWx0T3B0aW9uc1wiXG4gICAgICAgIHZhciB0ZW1wRm9yY2UgPSBvcHQuZm9yY2U7XG4gICAgICAgIG9wdC5zaW1wbGUgPSBmYWxzZTtcbiAgICAgICAgc2V0RGVmYXVsdE9wdGlvbnMoKTtcbiAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgb3B0LnVzZUNhY2hlID0gdGVtcENhY2hlO1xuICAgICAgICBvcHQuZm9yY2UgPSB0ZW1wRm9yY2U7XG4gICAgICAgIGNhY2hlID0ge307XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIFNldHMgZGVmYXVsdCB2YWx1ZSB0byByZXR1cm4gaWYgXCJnZXRcIiByZXNvbHZlcyB0byB1bmRlZmluZWRcbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtBbnl9IHZhbCBWYWx1ZSB3aGljaCB3aWxsIGJlIHJldHVybmVkIHdoZW4gXCJnZXRcIiByZXNvbHZlcyB0byB1bmRlZmluZWRcbiAgICAgKi9cbiAgICBfdGhpcy5zZXREZWZhdWx0UmV0dXJuVmFsID0gZnVuY3Rpb24odmFsKXtcbiAgICAgICAgb3B0WydkZWZhdWx0UmV0dXJuVmFsJ10gPSB2YWw7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIE1vZGlmeSB0aGUgcHJvcGVydHkgc2VwYXJhdG9yIGluIHRoZSBQYXRoVG9vbGtpdCBzeW50YXguXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSB2YWwgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoaXMgb3BlcmF0aW9uLlxuICAgICAqL1xuICAgIF90aGlzLnNldFNlcGFyYXRvclByb3BlcnR5ID0gZnVuY3Rpb24odmFsKXtcbiAgICAgICAgaWYgKHR5cGVvZiB2YWwgPT09ICRTVFJJTkcgJiYgdmFsLmxlbmd0aCA9PT0gMSl7XG4gICAgICAgICAgICBpZiAodmFsICE9PSAkV0lMRENBUkQgJiYgKCFvcHQuc2VwYXJhdG9yc1t2YWxdIHx8IG9wdC5zZXBhcmF0b3JzW3ZhbF0uZXhlYyA9PT0gJFBST1BFUlRZKSAmJiAhKG9wdC5wcmVmaXhlc1t2YWxdIHx8IG9wdC5jb250YWluZXJzW3ZhbF0pKXtcbiAgICAgICAgICAgICAgICB1cGRhdGVPcHRpb25DaGFyKG9wdC5zZXBhcmF0b3JzLCAkUFJPUEVSVFksIHZhbCk7XG4gICAgICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRTZXBhcmF0b3JQcm9wZXJ0eSAtIHZhbHVlIGFscmVhZHkgaW4gdXNlJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldFNlcGFyYXRvclByb3BlcnR5IC0gaW52YWxpZCB2YWx1ZScpO1xuICAgICAgICB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIE1vZGlmeSB0aGUgY29sbGVjdGlvbiBzZXBhcmF0b3IgaW4gdGhlIFBhdGhUb29sa2l0IHN5bnRheC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHZhbCBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhpcyBvcGVyYXRpb24uXG4gICAgICovXG4gICAgX3RoaXMuc2V0U2VwYXJhdG9yQ29sbGVjdGlvbiA9IGZ1bmN0aW9uKHZhbCl7XG4gICAgICAgIGlmICh0eXBlb2YgdmFsID09PSAkU1RSSU5HICYmIHZhbC5sZW5ndGggPT09IDEpe1xuICAgICAgICAgICAgaWYgKHZhbCAhPT0gJFdJTERDQVJEICYmICghb3B0LnNlcGFyYXRvcnNbdmFsXSB8fCBvcHQuc2VwYXJhdG9yc1t2YWxdLmV4ZWMgPT09ICRDT0xMRUNUSU9OKSAmJiAhKG9wdC5wcmVmaXhlc1t2YWxdIHx8IG9wdC5jb250YWluZXJzW3ZhbF0pKXtcbiAgICAgICAgICAgICAgICB1cGRhdGVPcHRpb25DaGFyKG9wdC5zZXBhcmF0b3JzLCAkQ09MTEVDVElPTiwgdmFsKTtcbiAgICAgICAgICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldFNlcGFyYXRvckNvbGxlY3Rpb24gLSB2YWx1ZSBhbHJlYWR5IGluIHVzZScpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRTZXBhcmF0b3JDb2xsZWN0aW9uIC0gaW52YWxpZCB2YWx1ZScpO1xuICAgICAgICB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIE1vZGlmeSB0aGUgcGFyZW50IHByZWZpeCBpbiB0aGUgUGF0aFRvb2xraXQgc3ludGF4LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gdmFsIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGlzIG9wZXJhdGlvbi5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRQcmVmaXhQYXJlbnQgPSBmdW5jdGlvbih2YWwpe1xuICAgICAgICBpZiAodHlwZW9mIHZhbCA9PT0gJFNUUklORyAmJiB2YWwubGVuZ3RoID09PSAxKXtcbiAgICAgICAgICAgIGlmICh2YWwgIT09ICRXSUxEQ0FSRCAmJiAoIW9wdC5wcmVmaXhlc1t2YWxdIHx8IG9wdC5wcmVmaXhlc1t2YWxdLmV4ZWMgPT09ICRQQVJFTlQpICYmICEob3B0LnNlcGFyYXRvcnNbdmFsXSB8fCBvcHQuY29udGFpbmVyc1t2YWxdKSl7XG4gICAgICAgICAgICAgICAgdXBkYXRlT3B0aW9uQ2hhcihvcHQucHJlZml4ZXMsICRQQVJFTlQsIHZhbCk7XG4gICAgICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRQcmVmaXhQYXJlbnQgLSB2YWx1ZSBhbHJlYWR5IGluIHVzZScpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRQcmVmaXhQYXJlbnQgLSBpbnZhbGlkIHZhbHVlJyk7XG4gICAgICAgIH1cbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogTW9kaWZ5IHRoZSByb290IHByZWZpeCBpbiB0aGUgUGF0aFRvb2xraXQgc3ludGF4LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gdmFsIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGlzIG9wZXJhdGlvbi5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRQcmVmaXhSb290ID0gZnVuY3Rpb24odmFsKXtcbiAgICAgICAgaWYgKHR5cGVvZiB2YWwgPT09ICRTVFJJTkcgJiYgdmFsLmxlbmd0aCA9PT0gMSl7XG4gICAgICAgICAgICBpZiAodmFsICE9PSAkV0lMRENBUkQgJiYgKCFvcHQucHJlZml4ZXNbdmFsXSB8fCBvcHQucHJlZml4ZXNbdmFsXS5leGVjID09PSAkUk9PVCkgJiYgIShvcHQuc2VwYXJhdG9yc1t2YWxdIHx8IG9wdC5jb250YWluZXJzW3ZhbF0pKXtcbiAgICAgICAgICAgICAgICB1cGRhdGVPcHRpb25DaGFyKG9wdC5wcmVmaXhlcywgJFJPT1QsIHZhbCk7XG4gICAgICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRQcmVmaXhSb290IC0gdmFsdWUgYWxyZWFkeSBpbiB1c2UnKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0UHJlZml4Um9vdCAtIGludmFsaWQgdmFsdWUnKTtcbiAgICAgICAgfVxuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBNb2RpZnkgdGhlIHBsYWNlaG9sZGVyIHByZWZpeCBpbiB0aGUgUGF0aFRvb2xraXQgc3ludGF4LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gdmFsIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGlzIG9wZXJhdGlvbi5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRQcmVmaXhQbGFjZWhvbGRlciA9IGZ1bmN0aW9uKHZhbCl7XG4gICAgICAgIGlmICh0eXBlb2YgdmFsID09PSAkU1RSSU5HICYmIHZhbC5sZW5ndGggPT09IDEpe1xuICAgICAgICAgICAgaWYgKHZhbCAhPT0gJFdJTERDQVJEICYmICghb3B0LnByZWZpeGVzW3ZhbF0gfHwgb3B0LnByZWZpeGVzW3ZhbF0uZXhlYyA9PT0gJFBMQUNFSE9MREVSKSAmJiAhKG9wdC5zZXBhcmF0b3JzW3ZhbF0gfHwgb3B0LmNvbnRhaW5lcnNbdmFsXSkpe1xuICAgICAgICAgICAgICAgIHVwZGF0ZU9wdGlvbkNoYXIob3B0LnByZWZpeGVzLCAkUExBQ0VIT0xERVIsIHZhbCk7XG4gICAgICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRQcmVmaXhQbGFjZWhvbGRlciAtIHZhbHVlIGFscmVhZHkgaW4gdXNlJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldFByZWZpeFBsYWNlaG9sZGVyIC0gaW52YWxpZCB2YWx1ZScpO1xuICAgICAgICB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIE1vZGlmeSB0aGUgY29udGV4dCBwcmVmaXggaW4gdGhlIFBhdGhUb29sa2l0IHN5bnRheC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHZhbCBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhpcyBvcGVyYXRpb24uXG4gICAgICovXG4gICAgX3RoaXMuc2V0UHJlZml4Q29udGV4dCA9IGZ1bmN0aW9uKHZhbCl7XG4gICAgICAgIGlmICh0eXBlb2YgdmFsID09PSAkU1RSSU5HICYmIHZhbC5sZW5ndGggPT09IDEpe1xuICAgICAgICAgICAgaWYgKHZhbCAhPT0gJFdJTERDQVJEICYmICghb3B0LnByZWZpeGVzW3ZhbF0gfHwgb3B0LnByZWZpeGVzW3ZhbF0uZXhlYyA9PT0gJENPTlRFWFQpICYmICEob3B0LnNlcGFyYXRvcnNbdmFsXSB8fCBvcHQuY29udGFpbmVyc1t2YWxdKSl7XG4gICAgICAgICAgICAgICAgdXBkYXRlT3B0aW9uQ2hhcihvcHQucHJlZml4ZXMsICRDT05URVhULCB2YWwpO1xuICAgICAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0UHJlZml4Q29udGV4dCAtIHZhbHVlIGFscmVhZHkgaW4gdXNlJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldFByZWZpeENvbnRleHQgLSBpbnZhbGlkIHZhbHVlJyk7XG4gICAgICAgIH1cbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogTW9kaWZ5IHRoZSBwcm9wZXJ0eSBjb250YWluZXIgY2hhcmFjdGVycyBpbiB0aGUgUGF0aFRvb2xraXQgc3ludGF4LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gdmFsIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGUgY29udGFpbmVyIG9wZW5lci5cbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gY2xvc2VyIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGUgY29udGFpbmVyIGNsb3Nlci5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRDb250YWluZXJQcm9wZXJ0eSA9IGZ1bmN0aW9uKHZhbCwgY2xvc2VyKXtcbiAgICAgICAgaWYgKHR5cGVvZiB2YWwgPT09ICRTVFJJTkcgJiYgdmFsLmxlbmd0aCA9PT0gMSAmJiB0eXBlb2YgY2xvc2VyID09PSAkU1RSSU5HICYmIGNsb3Nlci5sZW5ndGggPT09IDEpe1xuICAgICAgICAgICAgaWYgKHZhbCAhPT0gJFdJTERDQVJEICYmICghb3B0LmNvbnRhaW5lcnNbdmFsXSB8fCBvcHQuY29udGFpbmVyc1t2YWxdLmV4ZWMgPT09ICRQUk9QRVJUWSkgJiYgIShvcHQuc2VwYXJhdG9yc1t2YWxdIHx8IG9wdC5wcmVmaXhlc1t2YWxdKSl7XG4gICAgICAgICAgICAgICAgdXBkYXRlT3B0aW9uQ2hhcihvcHQuY29udGFpbmVycywgJFBST1BFUlRZLCB2YWwsIGNsb3Nlcik7XG4gICAgICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRDb250YWluZXJQcm9wZXJ0eSAtIHZhbHVlIGFscmVhZHkgaW4gdXNlJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldENvbnRhaW5lclByb3BlcnR5IC0gaW52YWxpZCB2YWx1ZScpO1xuICAgICAgICB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIE1vZGlmeSB0aGUgc2luZ2xlIHF1b3RlIGNvbnRhaW5lciBjaGFyYWN0ZXJzIGluIHRoZSBQYXRoVG9vbGtpdCBzeW50YXguXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSB2YWwgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoZSBjb250YWluZXIgb3BlbmVyLlxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBjbG9zZXIgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoZSBjb250YWluZXIgY2xvc2VyLlxuICAgICAqL1xuICAgIF90aGlzLnNldENvbnRhaW5lclNpbmdsZXF1b3RlID0gZnVuY3Rpb24odmFsLCBjbG9zZXIpe1xuICAgICAgICBpZiAodHlwZW9mIHZhbCA9PT0gJFNUUklORyAmJiB2YWwubGVuZ3RoID09PSAxICYmIHR5cGVvZiBjbG9zZXIgPT09ICRTVFJJTkcgJiYgY2xvc2VyLmxlbmd0aCA9PT0gMSl7XG4gICAgICAgICAgICBpZiAodmFsICE9PSAkV0lMRENBUkQgJiYgKCFvcHQuY29udGFpbmVyc1t2YWxdIHx8IG9wdC5jb250YWluZXJzW3ZhbF0uZXhlYyA9PT0gJFNJTkdMRVFVT1RFKSAmJiAhKG9wdC5zZXBhcmF0b3JzW3ZhbF0gfHwgb3B0LnByZWZpeGVzW3ZhbF0pKXtcbiAgICAgICAgICAgICAgICB1cGRhdGVPcHRpb25DaGFyKG9wdC5jb250YWluZXJzLCAkU0lOR0xFUVVPVEUsIHZhbCwgY2xvc2VyKTtcbiAgICAgICAgICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldENvbnRhaW5lclNpbmdsZXF1b3RlIC0gdmFsdWUgYWxyZWFkeSBpbiB1c2UnKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0Q29udGFpbmVyU2luZ2xlcXVvdGUgLSBpbnZhbGlkIHZhbHVlJyk7XG4gICAgICAgIH1cbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogTW9kaWZ5IHRoZSBkb3VibGUgcXVvdGUgY29udGFpbmVyIGNoYXJhY3RlcnMgaW4gdGhlIFBhdGhUb29sa2l0IHN5bnRheC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHZhbCBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhlIGNvbnRhaW5lciBvcGVuZXIuXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IGNsb3NlciBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhlIGNvbnRhaW5lciBjbG9zZXIuXG4gICAgICovXG4gICAgX3RoaXMuc2V0Q29udGFpbmVyRG91YmxlcXVvdGUgPSBmdW5jdGlvbih2YWwsIGNsb3Nlcil7XG4gICAgICAgIGlmICh0eXBlb2YgdmFsID09PSAkU1RSSU5HICYmIHZhbC5sZW5ndGggPT09IDEgJiYgdHlwZW9mIGNsb3NlciA9PT0gJFNUUklORyAmJiBjbG9zZXIubGVuZ3RoID09PSAxKXtcbiAgICAgICAgICAgIGlmICh2YWwgIT09ICRXSUxEQ0FSRCAmJiAoIW9wdC5jb250YWluZXJzW3ZhbF0gfHwgb3B0LmNvbnRhaW5lcnNbdmFsXS5leGVjID09PSAkRE9VQkxFUVVPVEUpICYmICEob3B0LnNlcGFyYXRvcnNbdmFsXSB8fCBvcHQucHJlZml4ZXNbdmFsXSkpe1xuICAgICAgICAgICAgICAgIHVwZGF0ZU9wdGlvbkNoYXIob3B0LmNvbnRhaW5lcnMsICRET1VCTEVRVU9URSwgdmFsLCBjbG9zZXIpO1xuICAgICAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0Q29udGFpbmVyRG91YmxlcXVvdGUgLSB2YWx1ZSBhbHJlYWR5IGluIHVzZScpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRDb250YWluZXJEb3VibGVxdW90ZSAtIGludmFsaWQgdmFsdWUnKTtcbiAgICAgICAgfVxuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBNb2RpZnkgdGhlIGZ1bmN0aW9uIGNhbGwgY29udGFpbmVyIGNoYXJhY3RlcnMgaW4gdGhlIFBhdGhUb29sa2l0IHN5bnRheC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHZhbCBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhlIGNvbnRhaW5lciBvcGVuZXIuXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IGNsb3NlciBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhlIGNvbnRhaW5lciBjbG9zZXIuXG4gICAgICovXG4gICAgX3RoaXMuc2V0Q29udGFpbmVyQ2FsbCA9IGZ1bmN0aW9uKHZhbCwgY2xvc2VyKXtcbiAgICAgICAgaWYgKHR5cGVvZiB2YWwgPT09ICRTVFJJTkcgJiYgdmFsLmxlbmd0aCA9PT0gMSAmJiB0eXBlb2YgY2xvc2VyID09PSAkU1RSSU5HICYmIGNsb3Nlci5sZW5ndGggPT09IDEpe1xuICAgICAgICAgICAgaWYgKHZhbCAhPT0gJFdJTERDQVJEICYmICghb3B0LmNvbnRhaW5lcnNbdmFsXSB8fCBvcHQuY29udGFpbmVyc1t2YWxdLmV4ZWMgPT09ICRDQUxMKSAmJiAhKG9wdC5zZXBhcmF0b3JzW3ZhbF0gfHwgb3B0LnByZWZpeGVzW3ZhbF0pKXtcbiAgICAgICAgICAgICAgICB1cGRhdGVPcHRpb25DaGFyKG9wdC5jb250YWluZXJzLCAkQ0FMTCwgdmFsLCBjbG9zZXIpO1xuICAgICAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0Q29udGFpbmVyQ2FsbCAtIHZhbHVlIGFscmVhZHkgaW4gdXNlJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldENvbnRhaW5lckNhbGwgLSBpbnZhbGlkIHZhbHVlJyk7XG4gICAgICAgIH1cbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogTW9kaWZ5IHRoZSBldmFsIHByb3BlcnR5IGNvbnRhaW5lciBjaGFyYWN0ZXJzIGluIHRoZSBQYXRoVG9vbGtpdCBzeW50YXguXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSB2YWwgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoZSBjb250YWluZXIgb3BlbmVyLlxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBjbG9zZXIgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoZSBjb250YWluZXIgY2xvc2VyLlxuICAgICAqL1xuICAgIF90aGlzLnNldENvbnRhaW5lckV2YWxQcm9wZXJ0eSA9IGZ1bmN0aW9uKHZhbCwgY2xvc2VyKXtcbiAgICAgICAgaWYgKHR5cGVvZiB2YWwgPT09ICRTVFJJTkcgJiYgdmFsLmxlbmd0aCA9PT0gMSAmJiB0eXBlb2YgY2xvc2VyID09PSAkU1RSSU5HICYmIGNsb3Nlci5sZW5ndGggPT09IDEpe1xuICAgICAgICAgICAgaWYgKHZhbCAhPT0gJFdJTERDQVJEICYmICghb3B0LmNvbnRhaW5lcnNbdmFsXSB8fCBvcHQuY29udGFpbmVyc1t2YWxdLmV4ZWMgPT09ICRFVkFMUFJPUEVSVFkpICYmICEob3B0LnNlcGFyYXRvcnNbdmFsXSB8fCBvcHQucHJlZml4ZXNbdmFsXSkpe1xuICAgICAgICAgICAgICAgIHVwZGF0ZU9wdGlvbkNoYXIob3B0LmNvbnRhaW5lcnMsICRFVkFMUFJPUEVSVFksIHZhbCwgY2xvc2VyKTtcbiAgICAgICAgICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldENvbnRhaW5lckV2YWxQcm9wZXJ0eSAtIHZhbHVlIGFscmVhZHkgaW4gdXNlJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldENvbnRhaW5lclByb3BlcnR5IC0gaW52YWxpZCB2YWx1ZScpO1xuICAgICAgICB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIFJlc2V0IGFsbCBQYXRoVG9vbGtpdCBvcHRpb25zIHRvIHRoZWlyIGRlZmF1bHQgdmFsdWVzLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKi9cbiAgICBfdGhpcy5yZXNldE9wdGlvbnMgPSBmdW5jdGlvbigpe1xuICAgICAgICBzZXREZWZhdWx0T3B0aW9ucygpO1xuICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICBjYWNoZSA9IHt9O1xuICAgIH07XG5cbiAgICAvLyBJbml0aWFsaXplIG9wdGlvbiBzZXRcbiAgICBzZXREZWZhdWx0T3B0aW9ucygpO1xuICAgIHVwZGF0ZVJlZ0V4KCk7XG5cbiAgICAvLyBBcHBseSBjdXN0b20gb3B0aW9ucyBpZiBwcm92aWRlZCBhcyBhcmd1bWVudCB0byBjb25zdHJ1Y3RvclxuICAgIG9wdGlvbnMgJiYgX3RoaXMuc2V0T3B0aW9ucyhvcHRpb25zKTtcblxufTtcblxuZXhwb3J0IGRlZmF1bHQgUGF0aFRvb2xraXQ7XG4iXSwibmFtZXMiOltdLCJtYXBwaW5ncyI6Ijs7Ozs7O0FBQUE7Ozs7Ozs7QUFPQSxBQUVBO0FBQ0EsSUFBSSxLQUFLLEdBQUcsQ0FBQyxTQUFTLENBQUMsQ0FBQyxDQUFDLE9BQU8sQ0FBQyxDQUFDLENBQUMsQ0FBQyxF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