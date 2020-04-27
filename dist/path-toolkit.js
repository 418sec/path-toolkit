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
        while (obj !== UNDEF && i < tkLength){
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

        path = path ? path : '';

        if(typeof isCircularCb !== $UNDEFINED && path){
            if(isCircularCb(obj, path)){
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
              more = scanForValue(obj[i], val, savePath, path ? path + propertySeparator + i : i, isCircularCb);
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
                    more = scanForValue(obj[keys[i]], val, savePath, path ? path + propertySeparator + prop : prop, isCircularCb);
                    if (!more){ return; }
                }
            }
            return true; // keep looking
        }
        // Leaf node (string, number, character, boolean, etc.), but didn't match
        return true; // keep looking
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

//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjpudWxsLCJzb3VyY2VzIjpbIi9ob21lL2Fhcm9uL3Byb2plY3RzL3BhdGgtdG9vbGtpdC9zcmMvcGF0aC10b29sa2l0LmpzIl0sInNvdXJjZXNDb250ZW50IjpbIi8qKlxuICogQGZpbGVPdmVydmlldyBQYXRoVG9vbGtpdCBldmFsdWF0ZXMgc3RyaW5nIHBhdGhzIGFzIHByb3BlcnR5L2luZGV4IHNlcXVlbmNlcyB3aXRoaW4gb2JqZWN0cyBhbmQgYXJyYXlzXG4gKiBAYXV0aG9yIEFhcm9uIEJyb3duXG4gKiBAdmVyc2lvbiAxLjEuMFxuICovXG5cbi8vIFBhcnNpbmcsIHRva2VuaW56aW5nLCBldGNcbid1c2Ugc3RyaWN0JztcblxuLy8gU29tZSBjb25zdGFudHMgZm9yIGNvbnZlbmllbmNlXG52YXIgVU5ERUYgPSAoZnVuY3Rpb24odSl7cmV0dXJuIHU7fSkoKTtcblxuLy8gU3RhdGljIHN0cmluZ3MsIGFzc2lnbmVkIHRvIGFpZCBjb2RlIG1pbmlmaWNhdGlvblxudmFyICRXSUxEQ0FSRCAgICAgPSAnKicsXG4gICAgJFVOREVGSU5FRCAgICA9ICd1bmRlZmluZWQnLFxuICAgICRTVFJJTkcgICAgICAgPSAnc3RyaW5nJyxcbiAgICAkUEFSRU5UICAgICAgID0gJ3BhcmVudCcsXG4gICAgJFJPT1QgICAgICAgICA9ICdyb290JyxcbiAgICAkUExBQ0VIT0xERVIgID0gJ3BsYWNlaG9sZGVyJyxcbiAgICAkQ09OVEVYVCAgICAgID0gJ2NvbnRleHQnLFxuICAgICRQUk9QRVJUWSAgICAgPSAncHJvcGVydHknLFxuICAgICRDT0xMRUNUSU9OICAgPSAnY29sbGVjdGlvbicsXG4gICAgJEVBQ0ggICAgICAgICA9ICdlYWNoJyxcbiAgICAkU0lOR0xFUVVPVEUgID0gJ3NpbmdsZXF1b3RlJyxcbiAgICAkRE9VQkxFUVVPVEUgID0gJ2RvdWJsZXF1b3RlJyxcbiAgICAkQ0FMTCAgICAgICAgID0gJ2NhbGwnLFxuICAgICRFVkFMUFJPUEVSVFkgPSAnZXZhbFByb3BlcnR5JztcblxuLyoqXG4gKiBUZXN0cyB3aGV0aGVyIGEgd2lsZGNhcmQgdGVtcGxhdGVzIG1hdGNoZXMgYSBnaXZlbiBzdHJpbmcuXG4gKiBgYGBqYXZhc2NyaXB0XG4gKiB2YXIgc3RyID0gJ2FhYWJiYnh4eGNjY2RkZCc7XG4gKiB3aWxkQ2FyZE1hdGNoKCdhYWFiYmJ4eHhjY2NkZGQnKTsgLy8gdHJ1ZVxuICogd2lsZENhcmRNYXRjaCgnKicsIHN0cik7IC8vIHRydWVcbiAqIHdpbGRDYXJkTWF0Y2goJyonLCAnJyk7IC8vIHRydWVcbiAqIHdpbGRDYXJkTWF0Y2goJ2EqJywgc3RyKTsgLy8gdHJ1ZVxuICogd2lsZENhcmRNYXRjaCgnYWEqZGRkJywgc3RyKTsgLy8gdHJ1ZVxuICogd2lsZENhcmRNYXRjaCgnKmQnLCBzdHIpOyAvLyB0cnVlXG4gKiB3aWxkQ2FyZE1hdGNoKCcqYScsIHN0cik7IC8vIGZhbHNlXG4gKiB3aWxkQ2FyZE1hdGNoKCdhKnonLCBzdHIpOyAvLyBmYWxzZVxuICogYGBgXG4gKiBAcHJpdmF0ZVxuICogQHBhcmFtICB7U3RyaW5nfSB0ZW1wbGF0ZSBXaWxkY2FyZCBwYXR0ZXJuXG4gKiBAcGFyYW0gIHtTdHJpbmd9IHN0ciAgICAgIFN0cmluZyB0byBtYXRjaCBhZ2FpbnN0IHdpbGRjYXJkIHBhdHRlcm5cbiAqIEByZXR1cm4ge0Jvb2xlYW59ICAgICAgICAgIFRydWUgaWYgcGF0dGVybiBtYXRjaGVzIHN0cmluZzsgRmFsc2UgaWYgbm90XG4gKi9cbnZhciB3aWxkQ2FyZE1hdGNoID0gZnVuY3Rpb24odGVtcGxhdGUsIHN0cil7XG4gICAgdmFyIHBvcyA9IHRlbXBsYXRlLmluZGV4T2YoJFdJTERDQVJEKSxcbiAgICAgICAgcGFydHMgPSB0ZW1wbGF0ZS5zcGxpdCgkV0lMRENBUkQsIDIpLFxuICAgICAgICBtYXRjaCA9IHRydWU7XG4gICAgaWYgKHBhcnRzWzBdKXtcbiAgICAgICAgLy8gSWYgbm8gd2lsZGNhcmQgcHJlc2VudCwgcmV0dXJuIHNpbXBsZSBzdHJpbmcgY29tcGFyaXNvblxuICAgICAgICBpZiAocGFydHNbMF0gPT09IHRlbXBsYXRlKXtcbiAgICAgICAgICAgIHJldHVybiBwYXJ0c1swXSA9PT0gc3RyO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgbWF0Y2ggPSBtYXRjaCAmJiBzdHIuc3Vic3RyKDAsIHBhcnRzWzBdLmxlbmd0aCkgPT09IHBhcnRzWzBdO1xuICAgICAgICB9XG4gICAgfVxuICAgIGlmIChwYXJ0c1sxXSl7XG4gICAgICAgIG1hdGNoID0gbWF0Y2ggJiYgc3RyLnN1YnN0cigtMSpwYXJ0c1sxXS5sZW5ndGgpID09PSBwYXJ0c1sxXTtcbiAgICB9XG4gICAgcmV0dXJuIG1hdGNoO1xufTtcblxuLyoqXG4gKiBJbnNwZWN0IGlucHV0IHZhbHVlIGFuZCBkZXRlcm1pbmUgd2hldGhlciBpdCBpcyBhbiBPYmplY3Qgb3Igbm90LlxuICogVmFsdWVzIG9mIHVuZGVmaW5lZCBhbmQgbnVsbCB3aWxsIHJldHVybiBcImZhbHNlXCIsIG90aGVyd2lzZVxuICogbXVzdCBiZSBvZiB0eXBlIFwib2JqZWN0XCIgb3IgXCJmdW5jdGlvblwiLlxuICogQHByaXZhdGVcbiAqIEBwYXJhbSAge09iamVjdH0gIHZhbCBUaGluZyB0byBleGFtaW5lLCBtYXkgYmUgb2YgYW55IHR5cGVcbiAqIEByZXR1cm4ge0Jvb2xlYW59ICAgICBUcnVlIGlmIHRoaW5nIGlzIG9mIHR5cGUgXCJvYmplY3RcIiBvciBcImZ1bmN0aW9uXCJcbiAqL1xudmFyIGlzT2JqZWN0ID0gZnVuY3Rpb24odmFsKXtcbiAgICBpZiAodHlwZW9mIHZhbCA9PT0gJFVOREVGSU5FRCB8fCB2YWwgPT09IG51bGwpIHsgcmV0dXJuIGZhbHNlO31cbiAgICByZXR1cm4gKCAodHlwZW9mIHZhbCA9PT0gJ2Z1bmN0aW9uJykgfHwgKHR5cGVvZiB2YWwgPT09ICdvYmplY3QnKSApO1xufTtcblxuLyoqXG4gKiBJbnNwZWN0IGlucHV0IHZhbHVlIGFuZCBkZXRlcm1pbmUgd2hldGhlciBpdCBpcyBhbiBJbnRlZ2VyIG9yIG5vdC5cbiAqIFZhbHVlcyBvZiB1bmRlZmluZWQgYW5kIG51bGwgd2lsbCByZXR1cm4gXCJmYWxzZVwiLlxuICogQHByaXZhdGVcbiAqIEBwYXJhbSAge1N0cmluZ30gIHZhbCBTdHJpbmcgdG8gZXhhbWluZVxuICogQHJldHVybiB7Qm9vbGVhbn0gICAgIFRydWUgaWYgdGhpbmcgY29uc2lzdHMgb2YgYXQgbGVhc3Qgb25lIGRpZ2l0IGFuZCBvbmx5IG9mIGRpZ2l0cyAobm8gLiBvciAsKVxuICovXG52YXIgZGlnaXRzUmVnZXggPSAvXlxcZCskLztcbnZhciBpc0RpZ2l0cyA9IGZ1bmN0aW9uKHZhbCl7XG4gICAgcmV0dXJuIGRpZ2l0c1JlZ2V4LnRlc3QodmFsKTtcbn07XG5cbi8qKlxuICogQ29udmVydCB2YXJpb3VzIHZhbHVlcyB0byB0cnVlIGJvb2xlYW4gYHRydWVgIG9yIGBmYWxzZWAuXG4gKiBGb3Igbm9uLXN0cmluZyB2YWx1ZXMsIHRoZSBuYXRpdmUgamF2YXNjcmlwdCBpZGVhIG9mIFwidHJ1ZVwiIHdpbGwgYXBwbHkuXG4gKiBGb3Igc3RyaW5nIHZhbHVlcywgdGhlIHdvcmRzIFwidHJ1ZVwiLCBcInllc1wiLCBhbmQgXCJvblwiIHdpbGwgYWxsIHJldHVybiBgdHJ1ZWAuXG4gKiBBbGwgb3RoZXIgc3RyaW5ncyByZXR1cm4gYGZhbHNlYC4gVGhlIHN0cmluZyBtYXRjaCBpcyBub24tY2FzZS1zZW5zaXRpdmUuXG4gKiBAcHJpdmF0ZVxuICovXG52YXIgdHJ1dGhpZnkgPSBmdW5jdGlvbih2YWwpe1xuICAgIHZhciB2O1xuICAgIGlmICh0eXBlb2YgdmFsICE9PSAkU1RSSU5HKXtcbiAgICAgICAgcmV0dXJuIHZhbCAmJiB0cnVlOyAvLyBVc2UgbmF0aXZlIGphdmFzY3JpcHQgbm90aW9uIG9mIFwidHJ1dGh5XCJcbiAgICB9XG4gICAgdiA9IHZhbC50b1VwcGVyQ2FzZSgpO1xuICAgIGlmICh2ID09PSAnVFJVRScgfHwgdiA9PT0gJ1lFUycgfHwgdiA9PT0gJ09OJyl7XG4gICAgICAgIHJldHVybiB0cnVlO1xuICAgIH1cbiAgICByZXR1cm4gZmFsc2U7XG59O1xuXG4vKipcbiAqIFVzaW5nIHByb3ZpZGVkIHF1b3RlIGNoYXJhY3RlciBhcyBwcmVmaXggYW5kIHN1ZmZpeCwgZXNjYXBlIGFueSBpbnN0YW5jZXNcbiAqIG9mIHRoZSBxdW90ZSBjaGFyYWN0ZXIgd2l0aGluIHRoZSBzdHJpbmcgYW5kIHJldHVybiBxdW90ZStzdHJpbmcrcXVvdGUuXG4gKiBUaGUgY2hhcmFjdGVyIGRlZmluZWQgYXMgXCJzaW5nbGVxdW90ZVwiIG1heSBiZSBhbHRlcmVkIGJ5IGN1c3RvbSBvcHRpb25zLFxuICogc28gYSBnZW5lcmFsLXB1cnBvc2UgZnVuY3Rpb24gaXMgbmVlZGVkIHRvIHF1b3RlIHBhdGggc2VnbWVudHMgY29ycmVjdGx5LlxuICogQHByaXZhdGVcbiAqIEBwYXJhbSAge1N0cmluZ30gcSAgIFNpbmdsZS1jaGFyYWN0ZXIgc3RyaW5nIHRvIHVzZSBhcyBxdW90ZSBjaGFyYWN0ZXJcbiAqIEBwYXJhbSAge1N0cmluZ30gc3RyIFN0cmluZyB0byBiZSBxdW90ZWQuXG4gKiBAcmV0dXJuIHtTdHJpbmd9ICAgICBPcmlnaW5hbCBzdHJpbmcsIHN1cnJvdW5kZWQgYnkgdGhlIHF1b3RlIGNoYXJhY3RlciwgcG9zc2libHkgbW9kaWZpZWQgaW50ZXJuYWxseSBpZiB0aGUgcXVvdGUgY2hhcmFjdGVyIGV4aXN0cyB3aXRoaW4gdGhlIHN0cmluZy5cbiAqL1xudmFyIHF1b3RlU3RyaW5nID0gZnVuY3Rpb24ocSwgc3RyKXtcbiAgICB2YXIgcVJlZ0V4ID0gbmV3IFJlZ0V4cChxLCAnZycpO1xuICAgIHJldHVybiBxICsgc3RyLnJlcGxhY2UocVJlZ0V4LCAnXFxcXCcgKyBxKSArIHE7XG59O1xuXG4vKipcbiAqIFBhdGhUb29sa2l0IGJhc2Ugb2JqZWN0LiBJbmNsdWRlcyBhbGwgaW5zdGFuY2Utc3BlY2lmaWMgZGF0YSAob3B0aW9ucywgY2FjaGUpXG4gKiBhcyBsb2NhbCB2YXJpYWJsZXMuIE1heSBiZSBwYXNzZWQgYW4gb3B0aW9ucyBoYXNoIHRvIHByZS1jb25maWd1cmUgdGhlXG4gKiBpbnN0YW5jZSBwcmlvciB0byB1c2UuXG4gKiBAY29uc3RydWN0b3JcbiAqIEBwcm9wZXJ0eSB7T2JqZWN0fSBvcHRpb25zIE9wdGlvbmFsLiBDb2xsZWN0aW9uIG9mIGNvbmZpZ3VyYXRpb24gc2V0dGluZ3MgZm9yIHRoaXMgaW5zdGFuY2Ugb2YgUGF0aFRvb2xraXQuIFNlZSBgc2V0T3B0aW9uc2AgZnVuY3Rpb24gYmVsb3cgZm9yIGRldGFpbGVkIGRvY3VtZW50YXRpb24uXG4gKi9cbnZhciBQYXRoVG9vbGtpdCA9IGZ1bmN0aW9uKG9wdGlvbnMpe1xuICAgIHZhciBfdGhpcyA9IHRoaXMsXG4gICAgICAgIGNhY2hlID0ge30sXG4gICAgICAgIG9wdCA9IHt9LFxuICAgICAgICBwcmVmaXhMaXN0LCBzZXBhcmF0b3JMaXN0LCBjb250YWluZXJMaXN0LCBjb250YWluZXJDbG9zZUxpc3QsXG4gICAgICAgIHByb3BlcnR5U2VwYXJhdG9yLFxuICAgICAgICBzaW5nbGVxdW90ZSwgZG91YmxlcXVvdGUsXG4gICAgICAgIHNpbXBsZVBhdGhDaGFycywgc2ltcGxlUGF0aFJlZ0V4LFxuICAgICAgICBhbGxTcGVjaWFscywgYWxsU3BlY2lhbHNSZWdFeCxcbiAgICAgICAgZXNjYXBlZE5vblNwZWNpYWxzUmVnRXgsXG4gICAgICAgIGVzY2FwZWRRdW90ZXMsXG4gICAgICAgIHdpbGRjYXJkUmVnRXg7XG5cbiAgICAvKipcbiAgICAgKiBTZXZlcmFsIHJlZ3VsYXIgZXhwcmVzc2lvbnMgYXJlIHByZS1jb21waWxlZCBmb3IgdXNlIGluIHBhdGggaW50ZXJwcmV0YXRpb24uXG4gICAgICogVGhlc2UgZXhwcmVzc2lvbnMgYXJlIGJ1aWx0IGZyb20gdGhlIGN1cnJlbnQgc3ludGF4IGNvbmZpZ3VyYXRpb24sIHNvIHRoZXlcbiAgICAgKiBtdXN0IGJlIHJlLWJ1aWx0IGV2ZXJ5IHRpbWUgdGhlIHN5bnRheCBjaGFuZ2VzLlxuICAgICAqIEBwcml2YXRlXG4gICAgICovXG4gICAgdmFyIHVwZGF0ZVJlZ0V4ID0gZnVuY3Rpb24oKXtcbiAgICAgICAgLy8gTGlzdHMgb2Ygc3BlY2lhbCBjaGFyYWN0ZXJzIGZvciB1c2UgaW4gcmVndWxhciBleHByZXNzaW9uc1xuICAgICAgICBwcmVmaXhMaXN0ID0gT2JqZWN0LmtleXMob3B0LnByZWZpeGVzKTtcbiAgICAgICAgc2VwYXJhdG9yTGlzdCA9IE9iamVjdC5rZXlzKG9wdC5zZXBhcmF0b3JzKTtcbiAgICAgICAgY29udGFpbmVyTGlzdCA9IE9iamVjdC5rZXlzKG9wdC5jb250YWluZXJzKTtcbiAgICAgICAgY29udGFpbmVyQ2xvc2VMaXN0ID0gY29udGFpbmVyTGlzdC5tYXAoZnVuY3Rpb24oa2V5KXsgcmV0dXJuIG9wdC5jb250YWluZXJzW2tleV0uY2xvc2VyOyB9KTtcblxuICAgICAgICBwcm9wZXJ0eVNlcGFyYXRvciA9ICcnO1xuICAgICAgICBPYmplY3Qua2V5cyhvcHQuc2VwYXJhdG9ycykuZm9yRWFjaChmdW5jdGlvbihzZXApeyBpZiAob3B0LnNlcGFyYXRvcnNbc2VwXS5leGVjID09PSAkUFJPUEVSVFkpeyBwcm9wZXJ0eVNlcGFyYXRvciA9IHNlcDsgfSB9KTtcbiAgICAgICAgc2luZ2xlcXVvdGUgPSAnJztcbiAgICAgICAgZG91YmxlcXVvdGUgPSAnJztcbiAgICAgICAgT2JqZWN0LmtleXMob3B0LmNvbnRhaW5lcnMpLmZvckVhY2goZnVuY3Rpb24oc2VwKXtcbiAgICAgICAgICAgIGlmIChvcHQuY29udGFpbmVyc1tzZXBdLmV4ZWMgPT09ICRTSU5HTEVRVU9URSl7IHNpbmdsZXF1b3RlID0gc2VwO31cbiAgICAgICAgICAgIGlmIChvcHQuY29udGFpbmVyc1tzZXBdLmV4ZWMgPT09ICRET1VCTEVRVU9URSl7IGRvdWJsZXF1b3RlID0gc2VwO31cbiAgICAgICAgfSk7XG5cbiAgICAgICAgLy8gRmluZCBhbGwgc3BlY2lhbCBjaGFyYWN0ZXJzIGV4Y2VwdCBwcm9wZXJ0eSBzZXBhcmF0b3IgKC4gYnkgZGVmYXVsdClcbiAgICAgICAgc2ltcGxlUGF0aENoYXJzID0gJ1tcXFxcXFxcXCcgKyBbJFdJTERDQVJEXS5jb25jYXQocHJlZml4TGlzdCkuY29uY2F0KHNlcGFyYXRvckxpc3QpLmNvbmNhdChjb250YWluZXJMaXN0KS5qb2luKCdcXFxcJykucmVwbGFjZSgnXFxcXCcrcHJvcGVydHlTZXBhcmF0b3IsICcnKSArICddJztcbiAgICAgICAgc2ltcGxlUGF0aFJlZ0V4ID0gbmV3IFJlZ0V4cChzaW1wbGVQYXRoQ2hhcnMpO1xuXG4gICAgICAgIC8vIEZpbmQgYWxsIHNwZWNpYWwgY2hhcmFjdGVycywgaW5jbHVkaW5nIGJhY2tzbGFzaFxuICAgICAgICBhbGxTcGVjaWFscyA9ICdbXFxcXFxcXFxcXFxcJyArIFskV0lMRENBUkRdLmNvbmNhdChwcmVmaXhMaXN0KS5jb25jYXQoc2VwYXJhdG9yTGlzdCkuY29uY2F0KGNvbnRhaW5lckxpc3QpLmNvbmNhdChjb250YWluZXJDbG9zZUxpc3QpLmpvaW4oJ1xcXFwnKSArICddJztcbiAgICAgICAgYWxsU3BlY2lhbHNSZWdFeCA9IG5ldyBSZWdFeHAoYWxsU3BlY2lhbHMsICdnJyk7XG5cbiAgICAgICAgLy8gRmluZCBhbGwgZXNjYXBlZCBzcGVjaWFsIGNoYXJhY3RlcnNcbiAgICAgICAgLy8gZXNjYXBlZFNwZWNpYWxzUmVnRXggPSBuZXcgUmVnRXhwKCdcXFxcJythbGxTcGVjaWFscywgJ2cnKTtcbiAgICAgICAgLy8gRmluZCBhbGwgZXNjYXBlZCBub24tc3BlY2lhbCBjaGFyYWN0ZXJzLCBpLmUuIHVubmVjZXNzYXJ5IGVzY2FwZXNcbiAgICAgICAgZXNjYXBlZE5vblNwZWNpYWxzUmVnRXggPSBuZXcgUmVnRXhwKCdcXFxcJythbGxTcGVjaWFscy5yZXBsYWNlKC9eXFxbLywnW14nKSk7XG4gICAgICAgIGlmIChzaW5nbGVxdW90ZSB8fCBkb3VibGVxdW90ZSl7XG4gICAgICAgICAgICBlc2NhcGVkUXVvdGVzID0gbmV3IFJlZ0V4cCgnXFxcXFsnK3NpbmdsZXF1b3RlK2RvdWJsZXF1b3RlKyddJywgJ2cnKTtcbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIGVzY2FwZWRRdW90ZXMgPSAnJztcbiAgICAgICAgfVxuXG4gICAgICAgIC8vIEZpbmQgd2lsZGNhcmQgY2hhcmFjdGVyXG4gICAgICAgIHdpbGRjYXJkUmVnRXggPSBuZXcgUmVnRXhwKCdcXFxcJyskV0lMRENBUkQpO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBTZXRzIGFsbCB0aGUgZGVmYXVsdCBvcHRpb25zIGZvciBpbnRlcnByZXRlciBiZWhhdmlvciBhbmQgc3ludGF4LlxuICAgICAqIEBwcml2YXRlXG4gICAgICovXG4gICAgdmFyIHNldERlZmF1bHRPcHRpb25zID0gZnVuY3Rpb24oKXtcbiAgICAgICAgb3B0ID0gb3B0IHx8IHt9O1xuICAgICAgICAvLyBEZWZhdWx0IHNldHRpbmdzXG4gICAgICAgIG9wdC51c2VDYWNoZSA9IHRydWU7ICAvLyBjYWNoZSB0b2tlbml6ZWQgcGF0aHMgZm9yIHJlcGVhdGVkIHVzZVxuICAgICAgICBvcHQuc2ltcGxlID0gZmFsc2U7ICAgLy8gb25seSBzdXBwb3J0IGRvdC1zZXBhcmF0ZWQgcGF0aHMsIG5vIG90aGVyIHNwZWNpYWwgY2hhcmFjdGVyc1xuICAgICAgICBvcHQuZm9yY2UgPSBmYWxzZTsgICAgLy8gY3JlYXRlIGludGVybWVkaWF0ZSBwcm9wZXJ0aWVzIGR1cmluZyBgc2V0YCBvcGVyYXRpb25cbiAgICAgICAgb3B0WydkZWZhdWx0UmV0dXJuVmFsJ10gPSBVTkRFRjsgICAvLyByZXR1cm4gdW5kZWZpbmVkIGJ5IGRlZmF1bHQgd2hlbiBwYXRoIHJlc29sdXRpb24gZmFpbHNcblxuICAgICAgICAvLyBEZWZhdWx0IHByZWZpeCBzcGVjaWFsIGNoYXJhY3RlcnNcbiAgICAgICAgb3B0LnByZWZpeGVzID0ge1xuICAgICAgICAgICAgJ14nOiB7XG4gICAgICAgICAgICAgICAgJ2V4ZWMnOiAkUEFSRU5UXG4gICAgICAgICAgICB9LFxuICAgICAgICAgICAgJ34nOiB7XG4gICAgICAgICAgICAgICAgJ2V4ZWMnOiAkUk9PVFxuICAgICAgICAgICAgfSxcbiAgICAgICAgICAgICclJzoge1xuICAgICAgICAgICAgICAgICdleGVjJzogJFBMQUNFSE9MREVSXG4gICAgICAgICAgICB9LFxuICAgICAgICAgICAgJ0AnOiB7XG4gICAgICAgICAgICAgICAgJ2V4ZWMnOiAkQ09OVEVYVFxuICAgICAgICAgICAgfVxuICAgICAgICB9O1xuICAgICAgICAvLyBEZWZhdWx0IHNlcGFyYXRvciBzcGVjaWFsIGNoYXJhY3RlcnNcbiAgICAgICAgb3B0LnNlcGFyYXRvcnMgPSB7XG4gICAgICAgICAgICAnLic6IHtcbiAgICAgICAgICAgICAgICAnZXhlYyc6ICRQUk9QRVJUWVxuICAgICAgICAgICAgICAgIH0sXG4gICAgICAgICAgICAnLCc6IHtcbiAgICAgICAgICAgICAgICAnZXhlYyc6ICRDT0xMRUNUSU9OXG4gICAgICAgICAgICAgICAgfSxcbiAgICAgICAgICAgICc8Jzoge1xuICAgICAgICAgICAgICAgICdleGVjJzogJEVBQ0hcbiAgICAgICAgICAgIH1cbiAgICAgICAgfTtcbiAgICAgICAgLy8gRGVmYXVsdCBjb250YWluZXIgc3BlY2lhbCBjaGFyYWN0ZXJzXG4gICAgICAgIG9wdC5jb250YWluZXJzID0ge1xuICAgICAgICAgICAgJ1snOiB7XG4gICAgICAgICAgICAgICAgJ2Nsb3Nlcic6ICddJyxcbiAgICAgICAgICAgICAgICAnZXhlYyc6ICRQUk9QRVJUWVxuICAgICAgICAgICAgICAgIH0sXG4gICAgICAgICAgICAnXFwnJzoge1xuICAgICAgICAgICAgICAgICdjbG9zZXInOiAnXFwnJyxcbiAgICAgICAgICAgICAgICAnZXhlYyc6ICRTSU5HTEVRVU9URVxuICAgICAgICAgICAgICAgIH0sXG4gICAgICAgICAgICAnXCInOiB7XG4gICAgICAgICAgICAgICAgJ2Nsb3Nlcic6ICdcIicsXG4gICAgICAgICAgICAgICAgJ2V4ZWMnOiAkRE9VQkxFUVVPVEVcbiAgICAgICAgICAgICAgICB9LFxuICAgICAgICAgICAgJygnOiB7XG4gICAgICAgICAgICAgICAgJ2Nsb3Nlcic6ICcpJyxcbiAgICAgICAgICAgICAgICAnZXhlYyc6ICRDQUxMXG4gICAgICAgICAgICAgICAgfSxcbiAgICAgICAgICAgICd7Jzoge1xuICAgICAgICAgICAgICAgICdjbG9zZXInOiAnfScsXG4gICAgICAgICAgICAgICAgJ2V4ZWMnOiAkRVZBTFBST1BFUlRZXG4gICAgICAgICAgICAgICAgfVxuICAgICAgICB9O1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBUZXN0IHN0cmluZyB0byBzZWUgaWYgaXQgaXMgc3Vycm91bmRlZCBieSBzaW5nbGUtIG9yIGRvdWJsZS1xdW90ZSwgdXNpbmcgdGhlXG4gICAgICogY3VycmVudCBjb25maWd1cmF0aW9uIGRlZmluaXRpb24gZm9yIHRob3NlIGNoYXJhY3RlcnMuIElmIG5vIHF1b3RlIGNvbnRhaW5lclxuICAgICAqIGlzIGRlZmluZWQsIHRoaXMgZnVuY3Rpb24gd2lsbCByZXR1cm4gZmFsc2Ugc2luY2UgaXQncyBub3QgcG9zc2libGUgdG8gcXVvdGVcbiAgICAgKiB0aGUgc3RyaW5nIGlmIHRoZXJlIGFyZSBubyBxdW90ZXMgaW4gdGhlIHN5bnRheC4gQWxzbyBpZ25vcmVzIGVzY2FwZWQgcXVvdGVcbiAgICAgKiBjaGFyYWN0ZXJzLlxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBzdHIgVGhlIHN0cmluZyB0byB0ZXN0IGZvciBlbmNsb3NpbmcgcXVvdGVzXG4gICAgICogQHJldHVybiB7Qm9vbGVhbn0gdHJ1ZSA9IHN0cmluZyBpcyBlbmNsb3NlZCBpbiBxdW90ZXM7IGZhbHNlID0gbm90IHF1b3RlZFxuICAgICAqL1xuICAgIHZhciBpc1F1b3RlZCA9IGZ1bmN0aW9uKHN0cil7XG4gICAgICAgIHZhciBjbGVhblN0ciA9IHN0ci5yZXBsYWNlKGVzY2FwZWRRdW90ZXMsICcnKTtcbiAgICAgICAgdmFyIHN0ckxlbiA9IGNsZWFuU3RyLmxlbmd0aDtcbiAgICAgICAgaWYgKHN0ckxlbiA8IDIpeyByZXR1cm4gZmFsc2U7IH1cbiAgICAgICAgcmV0dXJuICAoY2xlYW5TdHJbMF0gPT09IGNsZWFuU3RyW3N0ckxlbiAtIDFdKSAmJlxuICAgICAgICAgICAgICAgIChjbGVhblN0clswXSA9PT0gc2luZ2xlcXVvdGUgfHwgY2xlYW5TdHJbMF0gPT09IGRvdWJsZXF1b3RlKTtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogUmVtb3ZlIGVuY2xvc2luZyBxdW90ZXMgZnJvbSBhIHN0cmluZy4gVGhlIGlzUXVvdGVkIGZ1bmN0aW9uIHdpbGwgZGV0ZXJtaW5lXG4gICAgICogaWYgYW55IGNoYW5nZSBpcyBuZWVkZWQuIElmIHRoZSBzdHJpbmcgaXMgcXVvdGVkLCB3ZSBrbm93IHRoZSBmaXJzdCBhbmQgbGFzdFxuICAgICAqIGNoYXJhY3RlcnMgYXJlIHF1b3RlIG1hcmtzLCBzbyBzaW1wbHkgZG8gYSBzdHJpbmcgc2xpY2UuIElmIHRoZSBpbnB1dCB2YWx1ZSBpc1xuICAgICAqIG5vdCBxdW90ZWQsIHJldHVybiB0aGUgaW5wdXQgdmFsdWUgdW5jaGFuZ2VkLiBCZWNhdXNlIGlzUXVvdGVkIGlzIHVzZWQsIGlmXG4gICAgICogbm8gcXVvdGUgbWFya3MgYXJlIGRlZmluZWQgaW4gdGhlIHN5bnRheCwgdGhpcyBmdW5jdGlvbiB3aWxsIHJldHVybiB0aGUgaW5wdXQgdmFsdWUuXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHN0ciBUaGUgc3RyaW5nIHRvIHVuLXF1b3RlXG4gICAgICogQHJldHVybiB7U3RyaW5nfSBUaGUgaW5wdXQgc3RyaW5nIHdpdGhvdXQgYW55IGVuY2xvc2luZyBxdW90ZSBtYXJrcy5cbiAgICAgKi9cbiAgICB2YXIgc3RyaXBRdW90ZXMgPSBmdW5jdGlvbihzdHIpe1xuICAgICAgICBpZiAoaXNRdW90ZWQoc3RyKSl7XG4gICAgICAgICAgICByZXR1cm4gc3RyLnNsaWNlKDEsIC0xKTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gc3RyO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBTY2FuIGlucHV0IHN0cmluZyBmcm9tIGxlZnQgdG8gcmlnaHQsIG9uZSBjaGFyYWN0ZXIgYXQgYSB0aW1lLiBJZiBhIHNwZWNpYWwgY2hhcmFjdGVyXG4gICAgICogaXMgZm91bmQgKG9uZSBvZiBcInNlcGFyYXRvcnNcIiwgXCJjb250YWluZXJzXCIsIG9yIFwicHJlZml4ZXNcIiksIGVpdGhlciBzdG9yZSB0aGUgYWNjdW11bGF0ZWRcbiAgICAgKiB3b3JkIGFzIGEgdG9rZW4gb3IgZWxzZSBiZWdpbiB3YXRjaGluZyBpbnB1dCBmb3IgZW5kIG9mIHRva2VuIChmaW5kaW5nIGEgY2xvc2luZyBjaGFyYWN0ZXJcbiAgICAgKiBmb3IgYSBjb250YWluZXIgb3IgdGhlIGVuZCBvZiBhIGNvbGxlY3Rpb24pLiBJZiBhIGNvbnRhaW5lciBpcyBmb3VuZCwgY2FwdHVyZSB0aGUgc3Vic3RyaW5nXG4gICAgICogd2l0aGluIHRoZSBjb250YWluZXIgYW5kIHJlY3Vyc2l2ZWx5IGNhbGwgYHRva2VuaXplYCBvbiB0aGF0IHN1YnN0cmluZy4gRmluYWwgb3V0cHV0IHdpbGxcbiAgICAgKiBiZSBhbiBhcnJheSBvZiB0b2tlbnMuIEEgY29tcGxleCB0b2tlbiAobm90IGEgc2ltcGxlIHByb3BlcnR5IG9yIGluZGV4KSB3aWxsIGJlIHJlcHJlc2VudGVkXG4gICAgICogYXMgYW4gb2JqZWN0IGNhcnJ5aW5nIG1ldGFkYXRhIGZvciBwcm9jZXNzaW5nLlxuICAgICAqIEBwcml2YXRlXG4gICAgICogQHBhcmFtICB7U3RyaW5nfSBzdHIgUGF0aCBzdHJpbmdcbiAgICAgKiBAcmV0dXJuIHtBcnJheX0gICAgIEFycmF5IG9mIHRva2VucyBmb3VuZCBpbiB0aGUgaW5wdXQgcGF0aFxuICAgICAqL1xuICAgIHZhciB0b2tlbml6ZSA9IGZ1bmN0aW9uIChzdHIpe1xuICAgICAgICB2YXIgcGF0aCA9ICcnLFxuICAgICAgICAgICAgc2ltcGxlUGF0aCA9IHRydWUsIC8vIHBhdGggaXMgYXNzdW1lZCBcInNpbXBsZVwiIHVudGlsIHByb3ZlbiBvdGhlcndpc2VcbiAgICAgICAgICAgIHRva2VucyA9IFtdLFxuICAgICAgICAgICAgcmVjdXIgPSBbXSxcbiAgICAgICAgICAgIG1vZHMgPSB7fSxcbiAgICAgICAgICAgIHBhdGhMZW5ndGggPSAwLFxuICAgICAgICAgICAgd29yZCA9ICcnLFxuICAgICAgICAgICAgaGFzV2lsZGNhcmQgPSBmYWxzZSxcbiAgICAgICAgICAgIGRvRWFjaCA9IGZhbHNlLCAvLyBtdXN0IHJlbWVtYmVyIHRoZSBcImVhY2hcIiBvcGVyYXRvciBpbnRvIHRoZSBmb2xsb3dpbmcgdG9rZW5cbiAgICAgICAgICAgIHN1YnBhdGggPSAnJyxcbiAgICAgICAgICAgIGkgPSAwLFxuICAgICAgICAgICAgb3BlbmVyID0gJycsXG4gICAgICAgICAgICBjbG9zZXIgPSAnJyxcbiAgICAgICAgICAgIHNlcGFyYXRvciA9ICcnLFxuICAgICAgICAgICAgY29sbGVjdGlvbiA9IFtdLFxuICAgICAgICAgICAgZGVwdGggPSAwLFxuICAgICAgICAgICAgZXNjYXBlZCA9IDA7XG5cbiAgICAgICAgaWYgKG9wdC51c2VDYWNoZSAmJiBjYWNoZVtzdHJdICE9PSBVTkRFRil7IHJldHVybiBjYWNoZVtzdHJdOyB9XG5cbiAgICAgICAgLy8gU3RyaXAgb3V0IGFueSB1bm5lY2Vzc2FyeSBlc2NhcGluZyB0byBzaW1wbGlmeSBwcm9jZXNzaW5nIGJlbG93XG4gICAgICAgIHBhdGggPSBzdHIucmVwbGFjZShlc2NhcGVkTm9uU3BlY2lhbHNSZWdFeCwgJyQmJy5zdWJzdHIoMSkpO1xuICAgICAgICBwYXRoTGVuZ3RoID0gcGF0aC5sZW5ndGg7XG5cbiAgICAgICAgaWYgKHR5cGVvZiBzdHIgPT09ICRTVFJJTkcgJiYgIXNpbXBsZVBhdGhSZWdFeC50ZXN0KHN0cikpe1xuICAgICAgICAgICAgdG9rZW5zID0gcGF0aC5zcGxpdChwcm9wZXJ0eVNlcGFyYXRvcik7XG4gICAgICAgICAgICBvcHQudXNlQ2FjaGUgJiYgKGNhY2hlW3N0cl0gPSB7dDogdG9rZW5zLCBzaW1wbGU6IHNpbXBsZVBhdGh9KTtcbiAgICAgICAgICAgIHJldHVybiB7dDogdG9rZW5zLCBzaW1wbGU6IHNpbXBsZVBhdGh9O1xuICAgICAgICB9XG5cbiAgICAgICAgZm9yIChpID0gMDsgaSA8IHBhdGhMZW5ndGg7IGkrKyl7XG4gICAgICAgICAgICAvLyBTa2lwIGVzY2FwZSBjaGFyYWN0ZXIgKGBcXGApIGFuZCBzZXQgXCJlc2NhcGVkXCIgdG8gdGhlIGluZGV4IHZhbHVlXG4gICAgICAgICAgICAvLyBvZiB0aGUgY2hhcmFjdGVyIHRvIGJlIHRyZWF0ZWQgYXMgYSBsaXRlcmFsXG4gICAgICAgICAgICBpZiAoIWVzY2FwZWQgJiYgcGF0aFtpXSA9PT0gJ1xcXFwnKXtcbiAgICAgICAgICAgICAgICAvLyBOZXh0IGNoYXJhY3RlciBpcyB0aGUgZXNjYXBlZCBjaGFyYWN0ZXJcbiAgICAgICAgICAgICAgICBlc2NhcGVkID0gaSsxO1xuICAgICAgICAgICAgICAgIGkrKztcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIC8vIElmIGEgd2lsZGNhcmQgY2hhcmFjdGVyIGlzIGZvdW5kLCBtYXJrIHRoaXMgdG9rZW4gYXMgaGF2aW5nIGEgd2lsZGNhcmRcbiAgICAgICAgICAgIGlmIChwYXRoW2ldID09PSAkV0lMRENBUkQpIHtcbiAgICAgICAgICAgICAgICBoYXNXaWxkY2FyZCA9IHRydWU7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICAvLyBJZiB3ZSBoYXZlIGFscmVhZHkgcHJvY2Vzc2VkIGEgY29udGFpbmVyIG9wZW5lciwgdHJlYXQgdGhpcyBzdWJwYXRoIHNwZWNpYWxseVxuICAgICAgICAgICAgaWYgKGRlcHRoID4gMCl7XG4gICAgICAgICAgICAgICAgLy8gSXMgdGhpcyBjaGFyYWN0ZXIgYW5vdGhlciBvcGVuZXIgZnJvbSB0aGUgc2FtZSBjb250YWluZXI/IElmIHNvLCBhZGQgdG9cbiAgICAgICAgICAgICAgICAvLyB0aGUgZGVwdGggbGV2ZWwgc28gd2UgY2FuIG1hdGNoIHRoZSBjbG9zZXJzIGNvcnJlY3RseS4gKEV4Y2VwdCBmb3IgcXVvdGVzXG4gICAgICAgICAgICAgICAgLy8gd2hpY2ggY2Fubm90IGJlIG5lc3RlZClcbiAgICAgICAgICAgICAgICAvLyBJcyB0aGlzIGNoYXJhY3RlciB0aGUgY2xvc2VyPyBJZiBzbywgYmFjayBvdXQgb25lIGxldmVsIG9mIGRlcHRoLlxuICAgICAgICAgICAgICAgIC8vIEJlIGNhcmVmdWw6IHF1b3RlIGNvbnRhaW5lciB1c2VzIHNhbWUgY2hhcmFjdGVyIGZvciBvcGVuZXIgYW5kIGNsb3Nlci5cbiAgICAgICAgICAgICAgICAhZXNjYXBlZCAmJiBwYXRoW2ldID09PSBvcGVuZXIgJiYgb3BlbmVyICE9PSBjbG9zZXIuY2xvc2VyICYmIGRlcHRoKys7XG4gICAgICAgICAgICAgICAgIWVzY2FwZWQgJiYgcGF0aFtpXSA9PT0gY2xvc2VyLmNsb3NlciAmJiBkZXB0aC0tO1xuXG4gICAgICAgICAgICAgICAgLy8gV2hpbGUgc3RpbGwgaW5zaWRlIHRoZSBjb250YWluZXIsIGp1c3QgYWRkIHRvIHRoZSBzdWJwYXRoXG4gICAgICAgICAgICAgICAgaWYgKGRlcHRoID4gMCl7XG4gICAgICAgICAgICAgICAgICAgIHN1YnBhdGggKz0gcGF0aFtpXTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgLy8gV2hlbiB3ZSBjbG9zZSBvZmYgdGhlIGNvbnRhaW5lciwgdGltZSB0byBwcm9jZXNzIHRoZSBzdWJwYXRoIGFuZCBhZGQgcmVzdWx0cyB0byBvdXIgdG9rZW5zXG4gICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgIC8vIEhhbmRsZSBzdWJwYXRoIFwiW2Jhcl1cIiBpbiBmb28uW2Jhcl0sW2Jhel0gLSB3ZSBtdXN0IHByb2Nlc3Mgc3VicGF0aCBhbmQgY3JlYXRlIGEgbmV3IGNvbGxlY3Rpb25cbiAgICAgICAgICAgICAgICAgICAgaWYgKGkrMSA8IHBhdGhMZW5ndGggJiYgb3B0LnNlcGFyYXRvcnNbcGF0aFtpKzFdXSAmJiBvcHQuc2VwYXJhdG9yc1twYXRoW2krMV1dLmV4ZWMgPT09ICRDT0xMRUNUSU9OKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChzdWJwYXRoLmxlbmd0aCAmJiBjbG9zZXIuZXhlYyA9PT0gJFBST1BFUlRZKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHN0cmlwUXVvdGVzKHN1YnBhdGgpO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAoY2xvc2VyLmV4ZWMgPT09ICRTSU5HTEVRVU9URSB8fCBjbG9zZXIuZXhlYyA9PT0gJERPVUJMRVFVT1RFKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobW9kcy5oYXMpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHsndyc6IHN1YnBhdGgsICdtb2RzJzogbW9kcywgJ2RvRWFjaCc6IGRvRWFjaH07XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIHRva2Vucy5wdXNoKHdvcmQpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBtb2RzID0ge307XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gZmFsc2U7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHN1YnBhdGg7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gdHJ1ZTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHRva2VuaXplKHN1YnBhdGgpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChyZWN1ciA9PT0gVU5ERUYpeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIuZXhlYyA9IGNsb3Nlci5leGVjO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyLmRvRWFjaCA9IGRvRWFjaDtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIC8vIGNvbGxlY3Rpb24ucHVzaChjbG9zZXIuZXhlYyA9PT0gJFBST1BFUlRZID8gcmVjdXIudFswXSA6IHJlY3VyKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIGNvbGxlY3Rpb24ucHVzaChyZWN1cik7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgLy8gSGFuZGxlIHN1YnBhdGggXCJbYmF6XVwiIGluIGZvby5bYmFyXSxbYmF6XSAtIHdlIG11c3QgcHJvY2VzcyBzdWJwYXRoIGFuZCBhZGQgdG8gY29sbGVjdGlvblxuICAgICAgICAgICAgICAgICAgICBlbHNlIGlmIChjb2xsZWN0aW9uWzBdKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChzdWJwYXRoLmxlbmd0aCAmJiBjbG9zZXIuZXhlYyA9PT0gJFBST1BFUlRZKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHN0cmlwUXVvdGVzKHN1YnBhdGgpO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAoY2xvc2VyLmV4ZWMgPT09ICRTSU5HTEVRVU9URSB8fCBjbG9zZXIuZXhlYyA9PT0gJERPVUJMRVFVT1RFKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobW9kcy5oYXMpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHsndyc6IHN1YnBhdGgsICdtb2RzJzogbW9kcywgJ2RvRWFjaCc6IGRvRWFjaH07XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIHRva2Vucy5wdXNoKHdvcmQpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBtb2RzID0ge307XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gZmFsc2U7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHN1YnBhdGg7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gdHJ1ZTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZWN1ciA9IHRva2VuaXplKHN1YnBhdGgpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChyZWN1ciA9PT0gVU5ERUYpeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIuZXhlYyA9IGNsb3Nlci5leGVjO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyLmRvRWFjaCA9IGRvRWFjaDtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGNvbGxlY3Rpb24ucHVzaChyZWN1cik7XG4gICAgICAgICAgICAgICAgICAgICAgICB0b2tlbnMucHVzaCh7J3R0Jzpjb2xsZWN0aW9uLCAnZG9FYWNoJzpkb0VhY2h9KTtcbiAgICAgICAgICAgICAgICAgICAgICAgIGNvbGxlY3Rpb24gPSBbXTtcbiAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gZmFsc2U7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgLy8gU2ltcGxlIHByb3BlcnR5IGNvbnRhaW5lciBpcyBlcXVpdmFsZW50IHRvIGRvdC1zZXBhcmF0ZWQgdG9rZW4uIEp1c3QgYWRkIHRoaXMgdG9rZW4gdG8gdG9rZW5zLlxuICAgICAgICAgICAgICAgICAgICBlbHNlIGlmIChjbG9zZXIuZXhlYyA9PT0gJFBST1BFUlRZKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyID0ge3Q6W3N0cmlwUXVvdGVzKHN1YnBhdGgpXX07XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoZG9FYWNoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB0b2tlbnMucHVzaCh7J3cnOnJlY3VyLnRbMF0sICdtb2RzJzp7fSwgJ2RvRWFjaCc6dHJ1ZX0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gZmFsc2U7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZG9FYWNoID0gZmFsc2U7IC8vIHJlc2V0XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB0b2tlbnMucHVzaChyZWN1ci50WzBdKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IHRydWU7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgLy8gUXVvdGVkIHN1YnBhdGggaXMgYWxsIHRha2VuIGxpdGVyYWxseSB3aXRob3V0IHRva2VuIGV2YWx1YXRpb24uIEp1c3QgYWRkIHN1YnBhdGggdG8gdG9rZW5zIGFzLWlzLlxuICAgICAgICAgICAgICAgICAgICBlbHNlIGlmIChjbG9zZXIuZXhlYyA9PT0gJFNJTkdMRVFVT1RFIHx8IGNsb3Nlci5leGVjID09PSAkRE9VQkxFUVVPVEUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKG1vZHMuaGFzKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB3b3JkID0geyd3Jzogc3VicGF0aCwgJ21vZHMnOiBtb2RzLCAnZG9FYWNoJzogZG9FYWNofTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyB0b2tlbnMucHVzaCh3b3JkKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBtb2RzID0ge307XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgc2ltcGxlUGF0aCAmPSBmYWxzZTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHRva2Vucy5wdXNoKHN1YnBhdGgpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gdHJ1ZTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAvLyBPdGhlcndpc2UsIGNyZWF0ZSB0b2tlbiBvYmplY3QgdG8gaG9sZCB0b2tlbml6ZWQgc3VicGF0aCwgYWRkIHRvIHRva2Vucy5cbiAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoc3VicGF0aCA9PT0gJycpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJlY3VyID0ge3Q6W10sc2ltcGxlOnRydWV9O1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmVjdXIgPSB0b2tlbml6ZShzdWJwYXRoKTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChyZWN1ciA9PT0gVU5ERUYpeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICByZWN1ci5leGVjID0gY2xvc2VyLmV4ZWM7XG4gICAgICAgICAgICAgICAgICAgICAgICByZWN1ci5kb0VhY2ggPSBkb0VhY2g7XG4gICAgICAgICAgICAgICAgICAgICAgICB0b2tlbnMucHVzaChyZWN1cik7XG4gICAgICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IGZhbHNlO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIHN1YnBhdGggPSAnJzsgLy8gcmVzZXQgc3VicGF0aFxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIC8vIElmIGEgcHJlZml4IGNoYXJhY3RlciBpcyBmb3VuZCwgc3RvcmUgaXQgaW4gYG1vZHNgIGZvciBsYXRlciByZWZlcmVuY2UuXG4gICAgICAgICAgICAvLyBNdXN0IGtlZXAgY291bnQgZHVlIHRvIGBwYXJlbnRgIHByZWZpeCB0aGF0IGNhbiBiZSB1c2VkIG11bHRpcGxlIHRpbWVzIGluIG9uZSB0b2tlbi5cbiAgICAgICAgICAgIGVsc2UgaWYgKCFlc2NhcGVkICYmIHBhdGhbaV0gaW4gb3B0LnByZWZpeGVzICYmIG9wdC5wcmVmaXhlc1twYXRoW2ldXS5leGVjKXtcbiAgICAgICAgICAgICAgICBtb2RzLmhhcyA9IHRydWU7XG4gICAgICAgICAgICAgICAgaWYgKG1vZHNbb3B0LnByZWZpeGVzW3BhdGhbaV1dLmV4ZWNdKSB7IG1vZHNbb3B0LnByZWZpeGVzW3BhdGhbaV1dLmV4ZWNdKys7IH1cbiAgICAgICAgICAgICAgICBlbHNlIHsgbW9kc1tvcHQucHJlZml4ZXNbcGF0aFtpXV0uZXhlY10gPSAxOyB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICAvLyBJZiBhIHNlcGFyYXRvciBpcyBmb3VuZCwgdGltZSB0byBzdG9yZSB0aGUgdG9rZW4gd2UndmUgYmVlbiBhY2N1bXVsYXRpbmcuIElmXG4gICAgICAgICAgICAvLyB0aGlzIHRva2VuIGhhZCBhIHByZWZpeCwgd2Ugc3RvcmUgdGhlIHRva2VuIGFzIGFuIG9iamVjdCB3aXRoIG1vZGlmaWVyIGRhdGEuXG4gICAgICAgICAgICAvLyBJZiB0aGUgc2VwYXJhdG9yIGlzIHRoZSBjb2xsZWN0aW9uIHNlcGFyYXRvciwgd2UgbXVzdCBlaXRoZXIgY3JlYXRlIG9yIGFkZFxuICAgICAgICAgICAgLy8gdG8gYSBjb2xsZWN0aW9uIGZvciB0aGlzIHRva2VuLiBGb3Igc2ltcGxlIHNlcGFyYXRvciwgd2UgZWl0aGVyIGFkZCB0aGUgdG9rZW5cbiAgICAgICAgICAgIC8vIHRvIHRoZSB0b2tlbiBsaXN0IG9yIGVsc2UgYWRkIHRvIHRoZSBleGlzdGluZyBjb2xsZWN0aW9uIGlmIGl0IGV4aXN0cy5cbiAgICAgICAgICAgIGVsc2UgaWYgKCFlc2NhcGVkICYmIG9wdC5zZXBhcmF0b3JzW3BhdGhbaV1dICYmIG9wdC5zZXBhcmF0b3JzW3BhdGhbaV1dLmV4ZWMpe1xuICAgICAgICAgICAgICAgIHNlcGFyYXRvciA9IG9wdC5zZXBhcmF0b3JzW3BhdGhbaV1dO1xuICAgICAgICAgICAgICAgIGlmICghd29yZCAmJiAobW9kcy5oYXMgfHwgaGFzV2lsZGNhcmQpKXtcbiAgICAgICAgICAgICAgICAgICAgLy8gZm91bmQgYSBzZXBhcmF0b3IsIGFmdGVyIHNlZWluZyBwcmVmaXhlcywgYnV0IG5vIHRva2VuIHdvcmQgLT4gaW52YWxpZFxuICAgICAgICAgICAgICAgICAgICByZXR1cm4gdW5kZWZpbmVkO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAvLyBUaGlzIHRva2VuIHdpbGwgcmVxdWlyZSBzcGVjaWFsIGludGVycHJldGVyIHByb2Nlc3NpbmcgZHVlIHRvIHByZWZpeCBvciB3aWxkY2FyZC5cbiAgICAgICAgICAgICAgICBpZiAod29yZCAmJiAobW9kcy5oYXMgfHwgaGFzV2lsZGNhcmQgfHwgZG9FYWNoKSl7XG4gICAgICAgICAgICAgICAgICAgIHdvcmQgPSB7J3cnOiB3b3JkLCAnbW9kcyc6IG1vZHMsICdkb0VhY2gnOiBkb0VhY2h9O1xuICAgICAgICAgICAgICAgICAgICBtb2RzID0ge307XG4gICAgICAgICAgICAgICAgICAgIHNpbXBsZVBhdGggJj0gZmFsc2U7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIC8vIHdvcmQgaXMgYSBwbGFpbiBwcm9wZXJ0eSBvciBlbmQgb2YgY29sbGVjdGlvblxuICAgICAgICAgICAgICAgIGlmIChzZXBhcmF0b3IuZXhlYyA9PT0gJFBST1BFUlRZIHx8IHNlcGFyYXRvci5leGVjID09PSAkRUFDSCl7XG4gICAgICAgICAgICAgICAgICAgIC8vIHdlIGFyZSBnYXRoZXJpbmcgYSBjb2xsZWN0aW9uLCBzbyBhZGQgbGFzdCB3b3JkIHRvIGNvbGxlY3Rpb24gYW5kIHRoZW4gc3RvcmVcbiAgICAgICAgICAgICAgICAgICAgaWYgKGNvbGxlY3Rpb25bMF0gIT09IFVOREVGKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIHdvcmQgJiYgY29sbGVjdGlvbi5wdXNoKHdvcmQpO1xuICAgICAgICAgICAgICAgICAgICAgICAgdG9rZW5zLnB1c2goeyd0dCc6Y29sbGVjdGlvbiwgJ2RvRWFjaCc6ZG9FYWNofSk7XG4gICAgICAgICAgICAgICAgICAgICAgICBjb2xsZWN0aW9uID0gW107IC8vIHJlc2V0XG4gICAgICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IGZhbHNlO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIC8vIHdvcmQgaXMgYSBwbGFpbiBwcm9wZXJ0eVxuICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIHdvcmQgJiYgdG9rZW5zLnB1c2god29yZCk7XG4gICAgICAgICAgICAgICAgICAgICAgICBzaW1wbGVQYXRoICY9IHRydWU7XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgLy8gSWYgdGhlIHNlcGFyYXRvciBpcyB0aGUgXCJlYWNoXCIgc2VwYXJ0b3IsIHRoZSBmb2xsb3dpbmcgd29yZCB3aWxsIGJlIGV2YWx1YXRlZCBkaWZmZXJlbnRseS5cbiAgICAgICAgICAgICAgICAgICAgLy8gSWYgaXQncyBub3QgdGhlIFwiZWFjaFwiIHNlcGFyYXRvciwgdGhlbiByZXNldCBcImRvRWFjaFwiXG4gICAgICAgICAgICAgICAgICAgIGRvRWFjaCA9IHNlcGFyYXRvci5leGVjID09PSAkRUFDSDsgLy8gcmVzZXRcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgLy8gd29yZCBpcyBhIGNvbGxlY3Rpb25cbiAgICAgICAgICAgICAgICBlbHNlIGlmIChzZXBhcmF0b3IuZXhlYyA9PT0gJENPTExFQ1RJT04pe1xuICAgICAgICAgICAgICAgICAgICB3b3JkICYmIGNvbGxlY3Rpb24ucHVzaCh3b3JkKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgd29yZCA9ICcnOyAvLyByZXNldFxuICAgICAgICAgICAgICAgIGhhc1dpbGRjYXJkID0gZmFsc2U7IC8vIHJlc2V0XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICAvLyBGb3VuZCBhIGNvbnRhaW5lciBvcGVuaW5nIGNoYXJhY3Rlci4gQSBjb250YWluZXIgb3BlbmluZyBpcyBlcXVpdmFsZW50IHRvXG4gICAgICAgICAgICAvLyBmaW5kaW5nIGEgc2VwYXJhdG9yLCBzbyBcImZvby5iYXJcIiBpcyBlcXVpdmFsZW50IHRvIFwiZm9vW2Jhcl1cIiwgc28gYXBwbHkgc2ltaWxhclxuICAgICAgICAgICAgLy8gcHJvY2VzcyBhcyBzZXBhcmF0b3IgYWJvdmUgd2l0aCByZXNwZWN0IHRvIHRva2VuIHdlIGhhdmUgYWNjdW11bGF0ZWQgc28gZmFyLlxuICAgICAgICAgICAgLy8gRXhjZXB0IGluIGNhc2UgY29sbGVjdGlvbnMgLSBwYXRoIG1heSBoYXZlIGEgY29sbGVjdGlvbiBvZiBjb250YWluZXJzLCBzb1xuICAgICAgICAgICAgLy8gaW4gXCJmb29bYmFyXSxbYmF6XVwiLCB0aGUgXCJbYmFyXVwiIG1hcmtzIHRoZSBlbmQgb2YgdG9rZW4gXCJmb29cIiwgYnV0IFwiW2Jhel1cIiBpc1xuICAgICAgICAgICAgLy8gbWVyZWx5IGFub3RoZXIgZW50cnkgaW4gdGhlIGNvbGxlY3Rpb24sIHNvIHdlIGRvbid0IGNsb3NlIG9mZiB0aGUgY29sbGVjdGlvbiB0b2tlblxuICAgICAgICAgICAgLy8geWV0LlxuICAgICAgICAgICAgLy8gU2V0IGRlcHRoIHZhbHVlIGZvciBmdXJ0aGVyIHByb2Nlc3NpbmcuXG4gICAgICAgICAgICBlbHNlIGlmICghZXNjYXBlZCAmJiBvcHQuY29udGFpbmVyc1twYXRoW2ldXSAmJiBvcHQuY29udGFpbmVyc1twYXRoW2ldXS5leGVjKXtcbiAgICAgICAgICAgICAgICBjbG9zZXIgPSBvcHQuY29udGFpbmVyc1twYXRoW2ldXTtcbiAgICAgICAgICAgICAgICBpZiAod29yZCAmJiAobW9kcy5oYXMgfHwgaGFzV2lsZGNhcmQgfHwgZG9FYWNoKSl7XG4gICAgICAgICAgICAgICAgICAgIGlmICh0eXBlb2Ygd29yZCA9PT0gJ3N0cmluZycpe1xuICAgICAgICAgICAgICAgICAgICAgICAgd29yZCA9IHsndyc6IHdvcmQsICdtb2RzJzogbW9kcywgJ2RvRWFjaCc6ZG9FYWNofTtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIHdvcmQubW9kcyA9IG1vZHM7XG4gICAgICAgICAgICAgICAgICAgICAgICB3b3JkLmRvRWFjaCA9IGRvRWFjaDtcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICBtb2RzID0ge307XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGlmIChjb2xsZWN0aW9uWzBdICE9PSBVTkRFRil7XG4gICAgICAgICAgICAgICAgICAgIC8vIHdlIGFyZSBnYXRoZXJpbmcgYSBjb2xsZWN0aW9uLCBzbyBhZGQgbGFzdCB3b3JkIHRvIGNvbGxlY3Rpb24gYW5kIHRoZW4gc3RvcmVcbiAgICAgICAgICAgICAgICAgICAgd29yZCAmJiBjb2xsZWN0aW9uLnB1c2god29yZCk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAvLyB3b3JkIGlzIGEgcGxhaW4gcHJvcGVydHlcbiAgICAgICAgICAgICAgICAgICAgd29yZCAmJiB0b2tlbnMucHVzaCh3b3JkKTtcbiAgICAgICAgICAgICAgICAgICAgc2ltcGxlUGF0aCAmPSB0cnVlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBvcGVuZXIgPSBwYXRoW2ldO1xuICAgICAgICAgICAgICAgIC8vIDEpIGRvbid0IHJlc2V0IGRvRWFjaCBmb3IgZW1wdHkgd29yZCBiZWNhdXNlIHRoaXMgaXMgW2Zvb108W2Jhcl1cbiAgICAgICAgICAgICAgICAvLyAyKSBkb24ndCByZXNldCBkb0VhY2ggZm9yIG9wZW5pbmcgQ2FsbCBiZWNhdXNlIHRoaXMgaXMgYSxiPGZuKClcbiAgICAgICAgICAgICAgICBpZiAod29yZCAmJiBvcHQuY29udGFpbmVyc1tvcGVuZXJdLmV4ZWMgIT09ICRDQUxMKXtcbiAgICAgICAgICAgICAgICAgICAgZG9FYWNoID0gZmFsc2U7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIHdvcmQgPSAnJztcbiAgICAgICAgICAgICAgICBoYXNXaWxkY2FyZCA9IGZhbHNlO1xuICAgICAgICAgICAgICAgIGRlcHRoKys7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICAvLyBPdGhlcndpc2UsIHRoaXMgaXMganVzdCBhbm90aGVyIGNoYXJhY3RlciB0byBhZGQgdG8gdGhlIGN1cnJlbnQgdG9rZW5cbiAgICAgICAgICAgIGVsc2UgaWYgKGkgPCBwYXRoTGVuZ3RoKSB7XG4gICAgICAgICAgICAgICAgd29yZCArPSBwYXRoW2ldO1xuICAgICAgICAgICAgfVxuXG4gICAgICAgICAgICAvLyBJZiBjdXJyZW50IHBhdGggaW5kZXggbWF0Y2hlcyB0aGUgZXNjYXBlIGluZGV4IHZhbHVlLCByZXNldCBgZXNjYXBlZGBcbiAgICAgICAgICAgIGlmIChpIDwgcGF0aExlbmd0aCAmJiBpID09PSBlc2NhcGVkKXtcbiAgICAgICAgICAgICAgICBlc2NhcGVkID0gMDtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuXG4gICAgICAgIC8vIFBhdGggZW5kZWQgaW4gYW4gZXNjYXBlIGNoYXJhY3RlclxuICAgICAgICBpZiAoZXNjYXBlZCl7XG4gICAgICAgICAgICByZXR1cm4gdW5kZWZpbmVkO1xuICAgICAgICB9XG5cbiAgICAgICAgLy8gQWRkIHRyYWlsaW5nIHdvcmQgdG8gdG9rZW5zLCBpZiBwcmVzZW50XG4gICAgICAgIGlmICh0eXBlb2Ygd29yZCA9PT0gJ3N0cmluZycgJiYgd29yZCAmJiAobW9kcy5oYXMgfHwgaGFzV2lsZGNhcmQgfHwgZG9FYWNoKSl7XG4gICAgICAgICAgICB3b3JkID0geyd3Jzogd29yZCwgJ21vZHMnOiB3b3JkLm1vZHMgfHwgbW9kcywgJ2RvRWFjaCc6IGRvRWFjaH07XG4gICAgICAgICAgICBtb2RzID0ge307XG4gICAgICAgICAgICBzaW1wbGVQYXRoICY9IGZhbHNlO1xuICAgICAgICB9XG4gICAgICAgIGVsc2UgaWYgKHdvcmQgJiYgbW9kcy5oYXMpe1xuICAgICAgICAgICAgd29yZC5tb2RzID0gbW9kcztcbiAgICAgICAgfVxuICAgICAgICAvLyBXZSBhcmUgZ2F0aGVyaW5nIGEgY29sbGVjdGlvbiwgc28gYWRkIGxhc3Qgd29yZCB0byBjb2xsZWN0aW9uIGFuZCB0aGVuIHN0b3JlXG4gICAgICAgIGlmIChjb2xsZWN0aW9uWzBdICE9PSBVTkRFRil7XG4gICAgICAgICAgICB3b3JkICYmIGNvbGxlY3Rpb24ucHVzaCh3b3JkKTtcbiAgICAgICAgICAgIHRva2Vucy5wdXNoKHsndHQnOmNvbGxlY3Rpb24sICdkb0VhY2gnOmRvRWFjaH0pO1xuICAgICAgICAgICAgc2ltcGxlUGF0aCAmPSBmYWxzZTtcbiAgICAgICAgfVxuICAgICAgICAvLyBXb3JkIGlzIGEgcGxhaW4gcHJvcGVydHlcbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB3b3JkICYmIHRva2Vucy5wdXNoKHdvcmQpO1xuICAgICAgICAgICAgc2ltcGxlUGF0aCAmPSB0cnVlO1xuICAgICAgICB9XG5cbiAgICAgICAgLy8gZGVwdGggIT0gMCBtZWFucyBtaXNtYXRjaGVkIGNvbnRhaW5lcnNcbiAgICAgICAgaWYgKGRlcHRoICE9PSAwKXsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuXG4gICAgICAgIC8vIElmIHBhdGggd2FzIHZhbGlkLCBjYWNoZSB0aGUgcmVzdWx0XG4gICAgICAgIG9wdC51c2VDYWNoZSAmJiAoY2FjaGVbc3RyXSA9IHt0OiB0b2tlbnMsIHNpbXBsZTogc2ltcGxlUGF0aH0pO1xuXG4gICAgICAgIHJldHVybiB7dDogdG9rZW5zLCBzaW1wbGU6IHNpbXBsZVBhdGh9O1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBJdCBpcyBgcmVzb2x2ZVBhdGhgJ3Mgam9iIHRvIHRyYXZlcnNlIGFuIG9iamVjdCBhY2NvcmRpbmcgdG8gdGhlIHRva2Vuc1xuICAgICAqIGRlcml2ZWQgZnJvbSB0aGUga2V5cGF0aCBhbmQgZWl0aGVyIHJldHVybiB0aGUgdmFsdWUgZm91bmQgdGhlcmUgb3Igc2V0XG4gICAgICogYSBuZXcgdmFsdWUgaW4gdGhhdCBsb2NhdGlvbi5cbiAgICAgKiBUaGUgdG9rZW5zIGFyZSBhIHNpbXBsZSBhcnJheSBhbmQgYHJlb3NsdmVQYXRoYCBsb29wcyB0aHJvdWdoIHRoZSBsaXN0XG4gICAgICogd2l0aCBhIHNpbXBsZSBcIndoaWxlXCIgbG9vcC4gQSB0b2tlbiBtYXkgaXRzZWxmIGJlIGEgbmVzdGVkIHRva2VuIGFycmF5LFxuICAgICAqIHdoaWNoIGlzIHByb2Nlc3NlZCB0aHJvdWdoIHJlY3Vyc2lvbi5cbiAgICAgKiBBcyBlYWNoIHN1Y2Nlc3NpdmUgdmFsdWUgaXMgcmVzb2x2ZWQgd2l0aGluIGBvYmpgLCB0aGUgY3VycmVudCB2YWx1ZSBpc1xuICAgICAqIHB1c2hlZCBvbnRvIHRoZSBcInZhbHVlU3RhY2tcIiwgZW5hYmxpbmcgYmFja3dhcmQgcmVmZXJlbmNlcyAodXB3YXJkcyBpbiBgb2JqYClcbiAgICAgKiB0aHJvdWdoIHBhdGggcHJlZml4ZXMgbGlrZSBcIjxcIiBmb3IgXCJwYXJlbnRcIiBhbmQgXCJ+XCIgZm9yIFwicm9vdFwiLiBUaGUgbG9vcFxuICAgICAqIHNob3J0LWNpcmN1aXRzIGJ5IHJldHVybmluZyBgdW5kZWZpbmVkYCBpZiB0aGUgcGF0aCBpcyBpbnZhbGlkIGF0IGFueSBwb2ludCxcbiAgICAgKiBleGNlcHQgaW4gYHNldGAgc2NlbmFyaW8gd2l0aCBgZm9yY2VgIGVuYWJsZWQuXG4gICAgICogQHByaXZhdGVcbiAgICAgKiBAcGFyYW0gIHtPYmplY3R9IG9iaiAgICAgICAgVGhlIGRhdGEgb2JqZWN0IHRvIGJlIHJlYWQvd3JpdHRlblxuICAgICAqIEBwYXJhbSAge1N0cmluZ30gcGF0aCAgICAgICBUaGUga2V5cGF0aCB3aGljaCBgcmVzb2x2ZVBhdGhgIHdpbGwgZXZhbHVhdGUgYWdhaW5zdCBgb2JqYC4gTWF5IGJlIGEgcHJlLWNvbXBpbGVkIFRva2VucyBzZXQgaW5zdGVhZCBvZiBhIHN0cmluZy5cbiAgICAgKiBAcGFyYW0gIHtBbnl9IG5ld1ZhbHVlICAgVGhlIG5ldyB2YWx1ZSB0byBzZXQgYXQgdGhlIHBvaW50IGRlc2NyaWJlZCBieSBgcGF0aGAuIFVuZGVmaW5lZCBpZiB1c2VkIGluIGBnZXRgIHNjZW5hcmlvLlxuICAgICAqIEBwYXJhbSAge0FycmF5fSBhcmdzICAgICAgIEFycmF5IG9mIGV4dHJhIGFyZ3VtZW50cyB3aGljaCBtYXkgYmUgcmVmZXJlbmNlZCBieSBwbGFjZWhvbGRlcnMuIFVuZGVmaW5lZCBpZiBubyBleHRyYSBhcmd1bWVudHMgd2VyZSBnaXZlbi5cbiAgICAgKiBAcGFyYW0gIHtBcnJheX0gdmFsdWVTdGFjayBTdGFjayBvZiBvYmplY3QgY29udGV4dHMgYWNjdW11bGF0ZWQgYXMgdGhlIHBhdGggdG9rZW5zIGFyZSBwcm9jZXNzZWQgaW4gYG9iamBcbiAgICAgKiBAcmV0dXJuIHtBbnl9ICAgICAgICAgICAgSW4gYGdldGAsIHJldHVybnMgdGhlIHZhbHVlIGZvdW5kIGluIGBvYmpgIGF0IGBwYXRoYC4gSW4gYHNldGAsIHJldHVybnMgdGhlIG5ldyB2YWx1ZSB0aGF0IHdhcyBzZXQgaW4gYG9iamAuIElmIGBnZXRgIG9yIGBzZXRgIGFyZSBudG8gc3VjY2Vzc2Z1bCwgcmV0dXJucyBgdW5kZWZpbmVkYFxuICAgICAqL1xuICAgIHZhciByZXNvbHZlUGF0aCA9IGZ1bmN0aW9uIChvYmosIHBhdGgsIG5ld1ZhbHVlLCBhcmdzLCB2YWx1ZVN0YWNrKXtcbiAgICAgICAgdmFyIGNoYW5nZSA9IG5ld1ZhbHVlICE9PSBVTkRFRiwgLy8gYXJlIHdlIHNldHRpbmcgYSBuZXcgdmFsdWU/XG4gICAgICAgICAgICB0ayA9IFtdLFxuICAgICAgICAgICAgdGtMZW5ndGggPSAwLFxuICAgICAgICAgICAgdGtMYXN0SWR4ID0gMCxcbiAgICAgICAgICAgIHZhbHVlU3RhY2tMZW5ndGggPSAxLFxuICAgICAgICAgICAgaSA9IDAsIGogPSAwLFxuICAgICAgICAgICAgcHJldiA9IG9iaixcbiAgICAgICAgICAgIGN1cnIgPSAnJyxcbiAgICAgICAgICAgIGN1cnJMZW5ndGggPSAwLFxuICAgICAgICAgICAgZWFjaExlbmd0aCA9IDAsXG4gICAgICAgICAgICB3b3JkQ29weSA9ICcnLFxuICAgICAgICAgICAgY29udGV4dFByb3AsXG4gICAgICAgICAgICBpZHggPSAwLFxuICAgICAgICAgICAgY29udGV4dCA9IG9iaixcbiAgICAgICAgICAgIHJldCxcbiAgICAgICAgICAgIG5ld1ZhbHVlSGVyZSA9IGZhbHNlLFxuICAgICAgICAgICAgcGxhY2VJbnQgPSAwLFxuICAgICAgICAgICAgcHJvcCA9ICcnLFxuICAgICAgICAgICAgY2FsbEFyZ3M7XG5cbiAgICAgICAgLy8gRm9yIFN0cmluZyBwYXRoLCBlaXRoZXIgZmV0Y2ggdG9rZW5zIGZyb20gY2FjaGUgb3IgZnJvbSBgdG9rZW5pemVgLlxuICAgICAgICBpZiAodHlwZW9mIHBhdGggPT09ICRTVFJJTkcpe1xuICAgICAgICAgICAgaWYgKG9wdC51c2VDYWNoZSAmJiBjYWNoZVtwYXRoXSkgeyB0ayA9IGNhY2hlW3BhdGhdLnQ7IH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHRrID0gdG9rZW5pemUocGF0aCk7XG4gICAgICAgICAgICAgICAgaWYgKHRrID09PSBVTkRFRil7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgICAgICAgICB0ayA9IHRrLnQ7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgLy8gRm9yIGEgbm9uLXN0cmluZywgYXNzdW1lIGEgcHJlLWNvbXBpbGVkIHRva2VuIGFycmF5XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGsgPSBwYXRoLnQgPyBwYXRoLnQgOiBbcGF0aF07XG4gICAgICAgIH1cblxuICAgICAgICB0a0xlbmd0aCA9IHRrLmxlbmd0aDtcbiAgICAgICAgaWYgKHRrTGVuZ3RoID09PSAwKSB7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgdGtMYXN0SWR4ID0gdGtMZW5ndGggLSAxO1xuXG4gICAgICAgIC8vIHZhbHVlU3RhY2sgd2lsbCBiZSBhbiBhcnJheSBpZiB3ZSBhcmUgd2l0aGluIGEgcmVjdXJzaXZlIGNhbGwgdG8gYHJlc29sdmVQYXRoYFxuICAgICAgICBpZiAodmFsdWVTdGFjayl7XG4gICAgICAgICAgICB2YWx1ZVN0YWNrTGVuZ3RoID0gdmFsdWVTdGFjay5sZW5ndGg7XG4gICAgICAgIH1cbiAgICAgICAgLy8gT24gb3JpZ2luYWwgZW50cnkgdG8gYHJlc29sdmVQYXRoYCwgaW5pdGlhbGl6ZSB2YWx1ZVN0YWNrIHdpdGggdGhlIGJhc2Ugb2JqZWN0LlxuICAgICAgICAvLyB2YWx1ZVN0YWNrTGVuZ3RoIHdhcyBhbHJlYWR5IGluaXRpYWxpemVkIHRvIDEuXG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdmFsdWVTdGFjayA9IFtvYmpdO1xuICAgICAgICB9XG5cbiAgICAgICAgLy8gQ29udmVydGVkIEFycmF5LnJlZHVjZSBpbnRvIHdoaWxlIGxvb3AsIHN0aWxsIHVzaW5nIFwicHJldlwiLCBcImN1cnJcIiwgXCJpZHhcIlxuICAgICAgICAvLyBhcyBsb29wIHZhbHVlc1xuICAgICAgICB3aGlsZSAocHJldiAhPT0gVU5ERUYgJiYgaWR4IDwgdGtMZW5ndGgpe1xuICAgICAgICAgICAgY3VyciA9IHRrW2lkeF07XG5cbiAgICAgICAgICAgIC8vIElmIHdlIGFyZSBzZXR0aW5nIGEgbmV3IHZhbHVlIGFuZCB0aGlzIHRva2VuIGlzIHRoZSBsYXN0IHRva2VuLCB0aGlzXG4gICAgICAgICAgICAvLyBpcyB0aGUgcG9pbnQgd2hlcmUgdGhlIG5ldyB2YWx1ZSBtdXN0IGJlIHNldC5cbiAgICAgICAgICAgIG5ld1ZhbHVlSGVyZSA9IChjaGFuZ2UgJiYgKGlkeCA9PT0gdGtMYXN0SWR4KSk7XG5cbiAgICAgICAgICAgIC8vIEhhbmRsZSBtb3N0IGNvbW1vbiBzaW1wbGUgcGF0aCBzY2VuYXJpbyBmaXJzdFxuICAgICAgICAgICAgaWYgKHR5cGVvZiBjdXJyID09PSAkU1RSSU5HKXtcbiAgICAgICAgICAgICAgICAvLyBJZiB3ZSBhcmUgc2V0dGluZy4uLlxuICAgICAgICAgICAgICAgIGlmIChjaGFuZ2Upe1xuICAgICAgICAgICAgICAgICAgICAvLyBJZiB0aGlzIGlzIHRoZSBmaW5hbCB0b2tlbiB3aGVyZSB0aGUgbmV3IHZhbHVlIGdvZXMsIHNldCBpdFxuICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRbY3Vycl0gPSBuZXdWYWx1ZTtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjb250ZXh0W2N1cnJdICE9PSBuZXdWYWx1ZSl7IHJldHVybiB1bmRlZmluZWQ7IH0gLy8gbmV3IHZhbHVlIGZhaWxlZCB0byBzZXRcbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAvLyBGb3IgZWFybGllciB0b2tlbnMsIGNyZWF0ZSBvYmplY3QgcHJvcGVydGllcyBpZiBcImZvcmNlXCIgaXMgZW5hYmxlZFxuICAgICAgICAgICAgICAgICAgICBlbHNlIGlmIChvcHQuZm9yY2UgJiYgdHlwZW9mIGNvbnRleHRbY3Vycl0gPT09ICd1bmRlZmluZWQnKSB7XG4gICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0W2N1cnJdID0ge307XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgLy8gUmV0dXJuIHZhbHVlIGlzIGFzc2lnbmVkIGFzIHZhbHVlIG9mIHRoaXMgb2JqZWN0IHByb3BlcnR5XG4gICAgICAgICAgICAgICAgcmV0ID0gY29udGV4dFtjdXJyXTtcblxuICAgICAgICAgICAgICAgIC8vIFRoaXMgYmFzaWMgc3RydWN0dXJlIGlzIHJlcGVhdGVkIGluIG90aGVyIHNjZW5hcmlvcyBiZWxvdywgc28gdGhlIGxvZ2ljXG4gICAgICAgICAgICAgICAgLy8gcGF0dGVybiBpcyBvbmx5IGRvY3VtZW50ZWQgaGVyZSBmb3IgYnJldml0eS5cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIGlmIChjdXJyID09PSBVTkRFRil7XG4gICAgICAgICAgICAgICAgICAgIHJldCA9IHVuZGVmaW5lZDtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgZWxzZSBpZiAoY3Vyci50dCl7XG4gICAgICAgICAgICAgICAgICAgIC8vIENhbGwgcmVzb2x2ZVBhdGggYWdhaW4gd2l0aCBiYXNlIHZhbHVlIGFzIGV2YWx1YXRlZCB2YWx1ZSBzbyBmYXIgYW5kXG4gICAgICAgICAgICAgICAgICAgIC8vIGVhY2ggZWxlbWVudCBvZiBhcnJheSBhcyB0aGUgcGF0aC4gQ29uY2F0IGFsbCB0aGUgcmVzdWx0cyB0b2dldGhlci5cbiAgICAgICAgICAgICAgICAgICAgcmV0ID0gW107XG4gICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLmRvRWFjaCl7XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoIUFycmF5LmlzQXJyYXkoY29udGV4dCkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldHVybiB1bmRlZmluZWQ7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBqID0gMDtcbiAgICAgICAgICAgICAgICAgICAgICAgIGVhY2hMZW5ndGggPSBjb250ZXh0Lmxlbmd0aDtcblxuICAgICAgICAgICAgICAgICAgICAgICAgLy8gUGF0aCBsaWtlIEFycmF5LT5FYWNoLT5BcnJheSByZXF1aXJlcyBhIG5lc3RlZCBmb3IgbG9vcFxuICAgICAgICAgICAgICAgICAgICAgICAgLy8gdG8gcHJvY2VzcyB0aGUgdHdvIGFycmF5IGxheWVycy5cbiAgICAgICAgICAgICAgICAgICAgICAgIHdoaWxlKGogPCBlYWNoTGVuZ3RoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpID0gMDtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChbXSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgY3Vyckxlbmd0aCA9IGN1cnIudHQubGVuZ3RoO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHdoaWxlKGkgPCBjdXJyTGVuZ3RoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY3Vyci50dFtpXS5kb0VhY2ggPSBmYWxzZTsgLy8gVGhpcyBpcyBhIGhhY2ssIGRvbid0IGtub3cgaG93IGVsc2UgdG8gZGlzYWJsZSBcImRvRWFjaFwiIGZvciBjb2xsZWN0aW9uIG1lbWJlcnNcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKG5ld1ZhbHVlSGVyZSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0UHJvcCA9IHJlc29sdmVQYXRoKGNvbnRleHRbal0sIGN1cnIudHRbaV0sIG5ld1ZhbHVlLCBhcmdzLCB2YWx1ZVN0YWNrKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIGlmICh0eXBlb2YgY3Vyci50dFtpXSA9PT0gJ3N0cmluZycpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFByb3AgPSBjb250ZXh0W2pdW2N1cnIudHRbaV1dO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFByb3AgPSByZXNvbHZlUGF0aChjb250ZXh0W2pdLCBjdXJyLnR0W2ldLCB1bmRlZmluZWQsIGFyZ3MsIHZhbHVlU3RhY2spO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjb250ZXh0UHJvcCA9PT0gVU5ERUYpIHsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChuZXdWYWx1ZUhlcmUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIudHRbaV0udCAmJiBjdXJyLnR0W2ldLmV4ZWMgPT09ICRFVkFMUFJPUEVSVFkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRbal1bY29udGV4dFByb3BdID0gbmV3VmFsdWU7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldFtqXS5wdXNoKGNvbnRleHRQcm9wKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLnR0W2ldLnQgJiYgY3Vyci50dFtpXS5leGVjID09PSAkRVZBTFBST1BFUlRZKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXRbal0ucHVzaChjb250ZXh0W2pdW2NvbnRleHRQcm9wXSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldFtqXS5wdXNoKGNvbnRleHRQcm9wKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpKys7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGorKztcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgIGkgPSAwO1xuICAgICAgICAgICAgICAgICAgICAgICAgY3Vyckxlbmd0aCA9IGN1cnIudHQubGVuZ3RoO1xuICAgICAgICAgICAgICAgICAgICAgICAgd2hpbGUoaSA8IGN1cnJMZW5ndGgpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChuZXdWYWx1ZUhlcmUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0UHJvcCA9IHJlc29sdmVQYXRoKGNvbnRleHQsIGN1cnIudHRbaV0sIG5ld1ZhbHVlLCBhcmdzLCB2YWx1ZVN0YWNrKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAodHlwZW9mIGN1cnIudHRbaV0gPT09ICdzdHJpbmcnKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFByb3AgPSBjb250ZXh0W2N1cnIudHRbaV1dO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFByb3AgPSByZXNvbHZlUGF0aChjb250ZXh0LCBjdXJyLnR0W2ldLCB1bmRlZmluZWQsIGFyZ3MsIHZhbHVlU3RhY2spO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY29udGV4dFByb3AgPT09IFVOREVGKSB7IHJldHVybiB1bmRlZmluZWQ7IH1cblxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChuZXdWYWx1ZUhlcmUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci50dFtpXS50ICYmIGN1cnIudHRbaV0uZXhlYyA9PT0gJEVWQUxQUk9QRVJUWSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0W2NvbnRleHRQcm9wXSA9IG5ld1ZhbHVlO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goY29udGV4dFByb3ApO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci50dFtpXS50ICYmIGN1cnIudHRbaV0uZXhlYyA9PT0gJEVWQUxQUk9QRVJUWSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChjb250ZXh0W2NvbnRleHRQcm9wXSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChjb250ZXh0UHJvcCk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaSsrO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGVsc2UgaWYgKGN1cnIudyl7XG4gICAgICAgICAgICAgICAgICAgIC8vIHRoaXMgd29yZCB0b2tlbiBoYXMgbW9kaWZpZXJzXG4gICAgICAgICAgICAgICAgICAgIHdvcmRDb3B5ID0gY3Vyci53O1xuICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci5tb2RzLmhhcyl7XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci5tb2RzLnBhcmVudCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gbW9kaWZ5IGN1cnJlbnQgY29udGV4dCwgc2hpZnQgdXB3YXJkcyBpbiBiYXNlIG9iamVjdCBvbmUgbGV2ZWxcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0ID0gdmFsdWVTdGFja1t2YWx1ZVN0YWNrTGVuZ3RoIC0gMSAtIGN1cnIubW9kcy5wYXJlbnRdO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjb250ZXh0ID09PSBVTkRFRikgeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci5tb2RzLnJvb3Qpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIFJlc2V0IGNvbnRleHQgYW5kIHZhbHVlU3RhY2ssIHN0YXJ0IG92ZXIgYXQgcm9vdCBpbiB0aGlzIGNvbnRleHRcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0ID0gdmFsdWVTdGFja1swXTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB2YWx1ZVN0YWNrID0gW2NvbnRleHRdO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHZhbHVlU3RhY2tMZW5ndGggPSAxO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIubW9kcy5wbGFjZWhvbGRlcil7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcGxhY2VJbnQgPSB3b3JkQ29weSAtIDE7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGFyZ3NbcGxhY2VJbnRdID09PSBVTkRFRil7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBGb3JjZSBhcmdzW3BsYWNlSW50XSB0byBTdHJpbmcsIHdvbid0IGF0dGVtcHQgdG8gcHJvY2Vzc1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIGFyZyBvZiB0eXBlIGZ1bmN0aW9uLCBhcnJheSwgb3IgcGxhaW4gb2JqZWN0XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgd29yZENvcHkgPSBhcmdzW3BsYWNlSW50XS50b1N0cmluZygpO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICB9XG5cbiAgICAgICAgICAgICAgICAgICAgLy8gZG9FYWNoIG9wdGlvbiBtZWFucyB0byB0YWtlIGFsbCB2YWx1ZXMgaW4gY29udGV4dCAobXVzdCBiZSBhbiBhcnJheSksIGFwcGx5XG4gICAgICAgICAgICAgICAgICAgIC8vIFwiY3VyclwiIHRvIGVhY2ggb25lLCBhbmQgcmV0dXJuIHRoZSBuZXcgYXJyYXkuIE9wZXJhdGVzIGxpa2UgQXJyYXkubWFwLlxuICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci5kb0VhY2gpe1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKCFBcnJheS5pc0FycmF5KGNvbnRleHQpKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXR1cm4gdW5kZWZpbmVkO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gW107XG4gICAgICAgICAgICAgICAgICAgICAgICBpID0gMDtcbiAgICAgICAgICAgICAgICAgICAgICAgIGVhY2hMZW5ndGggPSBjb250ZXh0Lmxlbmd0aDtcbiAgICAgICAgICAgICAgICAgICAgICAgIHdoaWxlKGkgPCBlYWNoTGVuZ3RoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBcImNvbnRleHRcIiBtb2RpZmllciAoXCJAXCIgYnkgZGVmYXVsdCkgcmVwbGFjZXMgY3VycmVudCBjb250ZXh0IHdpdGggYSB2YWx1ZSBmcm9tXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gdGhlIGFyZ3VtZW50cy5cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci5tb2RzLmNvbnRleHQpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoaXNEaWdpdHMod29yZENvcHkpKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHBsYWNlSW50ID0gd29yZENvcHkgLSAxO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGFyZ3NbcGxhY2VJbnRdID09PSBVTkRFRil7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIEZvcmNlIGFyZ3NbcGxhY2VJbnRdIHRvIFN0cmluZywgd29uJ3QgYXR3b3JkQ29weXQgdG8gcHJvY2Vzc1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gYXJnIG9mIHR5cGUgZnVuY3Rpb24sIGFycmF5LCBvciBwbGFpbiBvYmplY3RcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKGFyZ3NbcGxhY2VJbnRdKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldCA9IHdvcmRDb3B5O1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBSZXBlYXQgYmFzaWMgc3RyaW5nIHByb3BlcnR5IHByb2Nlc3Npbmcgd2l0aCB3b3JkIGFuZCBtb2RpZmllZCBjb250ZXh0XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjb250ZXh0W2ldW3dvcmRDb3B5XSAhPT0gVU5ERUYpIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChuZXdWYWx1ZUhlcmUpeyBjb250ZXh0W2ldW3dvcmRDb3B5XSA9IG5ld1ZhbHVlOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChjb250ZXh0W2ldW3dvcmRDb3B5XSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAodHlwZW9mIGNvbnRleHRbaV0gPT09ICdmdW5jdGlvbicpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2god29yZENvcHkpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIFBsYWluIHByb3BlcnR5IHRva2VucyBhcmUgbGlzdGVkIGFzIHNwZWNpYWwgd29yZCB0b2tlbnMgd2hlbmV2ZXJcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gYSB3aWxkY2FyZCBpcyBmb3VuZCB3aXRoaW4gdGhlIHByb3BlcnR5IHN0cmluZy4gQSB3aWxkY2FyZCBpbiBhXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIHByb3BlcnR5IGNhdXNlcyBhbiBhcnJheSBvZiBtYXRjaGluZyBwcm9wZXJ0aWVzIHRvIGJlIHJldHVybmVkLFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBzbyBsb29wIHRocm91Z2ggYWxsIHByb3BlcnRpZXMgYW5kIGV2YWx1YXRlIHRva2VuIGZvciBldmVyeVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBwcm9wZXJ0eSB3aGVyZSBgd2lsZENhcmRNYXRjaGAgcmV0dXJucyB0cnVlLlxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIGlmICh3aWxkY2FyZFJlZ0V4LnRlc3Qod29yZENvcHkpKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKFtdKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGZvciAocHJvcCBpbiBjb250ZXh0W2ldKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAod2lsZENhcmRNYXRjaCh3b3JkQ29weSwgcHJvcCkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXsgY29udGV4dFtpXVtwcm9wXSA9IG5ld1ZhbHVlOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldFtpXS5wdXNoKGNvbnRleHRbaV1bcHJvcF0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpKys7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAvLyBcImNvbnRleHRcIiBtb2RpZmllciAoXCJAXCIgYnkgZGVmYXVsdCkgcmVwbGFjZXMgY3VycmVudCBjb250ZXh0IHdpdGggYSB2YWx1ZSBmcm9tXG4gICAgICAgICAgICAgICAgICAgICAgICAvLyB0aGUgYXJndW1lbnRzLlxuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIubW9kcy5jb250ZXh0KXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoaXNEaWdpdHMod29yZENvcHkpKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcGxhY2VJbnQgPSB3b3JkQ29weSAtIDE7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChhcmdzW3BsYWNlSW50XSA9PT0gVU5ERUYpeyByZXR1cm4gdW5kZWZpbmVkOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIEZvcmNlIGFyZ3NbcGxhY2VJbnRdIHRvIFN0cmluZywgd29uJ3QgYXR3b3JkQ29weXQgdG8gcHJvY2Vzc1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBhcmcgb2YgdHlwZSBmdW5jdGlvbiwgYXJyYXksIG9yIHBsYWluIG9iamVjdFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQgPSBhcmdzW3BsYWNlSW50XTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQgPSB3b3JkQ29weTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBSZXBlYXQgYmFzaWMgc3RyaW5nIHByb3BlcnR5IHByb2Nlc3Npbmcgd2l0aCB3b3JkIGFuZCBtb2RpZmllZCBjb250ZXh0XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGNvbnRleHRbd29yZENvcHldICE9PSBVTkRFRikge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXsgY29udGV4dFt3b3JkQ29weV0gPSBuZXdWYWx1ZTsgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQgPSBjb250ZXh0W3dvcmRDb3B5XTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAodHlwZW9mIGNvbnRleHQgPT09ICdmdW5jdGlvbicpe1xuXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldCA9IHdvcmRDb3B5O1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBQbGFpbiBwcm9wZXJ0eSB0b2tlbnMgYXJlIGxpc3RlZCBhcyBzcGVjaWFsIHdvcmQgdG9rZW5zIHdoZW5ldmVyXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gYSB3aWxkY2FyZCBpcyBmb3VuZCB3aXRoaW4gdGhlIHByb3BlcnR5IHN0cmluZy4gQSB3aWxkY2FyZCBpbiBhXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gcHJvcGVydHkgY2F1c2VzIGFuIGFycmF5IG9mIG1hdGNoaW5nIHByb3BlcnRpZXMgdG8gYmUgcmV0dXJuZWQsXG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgLy8gc28gbG9vcCB0aHJvdWdoIGFsbCBwcm9wZXJ0aWVzIGFuZCBldmFsdWF0ZSB0b2tlbiBmb3IgZXZlcnlcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAvLyBwcm9wZXJ0eSB3aGVyZSBgd2lsZENhcmRNYXRjaGAgcmV0dXJucyB0cnVlLlxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2UgaWYgKHdpbGRjYXJkUmVnRXgudGVzdCh3b3JkQ29weSkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQgPSBbXTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgZm9yIChwcm9wIGluIGNvbnRleHQpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgaWYgKHdpbGRDYXJkTWF0Y2god29yZENvcHksIHByb3ApKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXsgY29udGV4dFtwcm9wXSA9IG5ld1ZhbHVlOyB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goY29udGV4dFtwcm9wXSk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAvLyBFdmFsIFByb3BlcnR5IHRva2VucyBvcGVyYXRlIG9uIGEgdGVtcG9yYXJ5IGNvbnRleHQgY3JlYXRlZCBieVxuICAgICAgICAgICAgICAgIC8vIHJlY3Vyc2l2ZWx5IGNhbGxpbmcgYHJlc29sdmVQYXRoYCB3aXRoIGEgY29weSBvZiB0aGUgdmFsdWVTdGFjay5cbiAgICAgICAgICAgICAgICBlbHNlIGlmIChjdXJyLmV4ZWMgPT09ICRFVkFMUFJPUEVSVFkpe1xuICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci5kb0VhY2gpe1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKCFBcnJheS5pc0FycmF5KGNvbnRleHQpKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXR1cm4gdW5kZWZpbmVkO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gW107XG4gICAgICAgICAgICAgICAgICAgICAgICBpID0gMDtcbiAgICAgICAgICAgICAgICAgICAgICAgIGVhY2hMZW5ndGggPSBjb250ZXh0Lmxlbmd0aDtcbiAgICAgICAgICAgICAgICAgICAgICAgIHdoaWxlKGkgPCBlYWNoTGVuZ3RoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci5zaW1wbGUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNvbnRleHRbaV1bX3RoaXMuZ2V0KGNvbnRleHRbaV0sIHt0OmN1cnIudCwgc2ltcGxlOnRydWV9KV0gPSBuZXdWYWx1ZTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChjb250ZXh0W2ldW190aGlzLmdldChjb250ZXh0W2ldLCB7dDpjdXJyLnQsIHNpbXBsZTp0cnVlfSldKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChuZXdWYWx1ZUhlcmUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFtpXVtyZXNvbHZlUGF0aChjb250ZXh0W2ldLCBjdXJyLCBVTkRFRiwgYXJncywgdmFsdWVTdGFjayldID0gbmV3VmFsdWU7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goY29udGV4dFtpXVtyZXNvbHZlUGF0aChjb250ZXh0W2ldLCBjdXJyLCBVTkRFRiwgYXJncywgdmFsdWVTdGFjayldKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaSsrO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIuc2ltcGxlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAobmV3VmFsdWVIZXJlKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY29udGV4dFtfdGhpcy5nZXQoY29udGV4dCwge3Q6IGN1cnIudCwgc2ltcGxlOnRydWV9KV0gPSBuZXdWYWx1ZTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gY29udGV4dFtfdGhpcy5nZXQoY29udGV4dCwge3Q6Y3Vyci50LCBzaW1wbGU6dHJ1ZX0pXTtcbiAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChuZXdWYWx1ZUhlcmUpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBjb250ZXh0W3Jlc29sdmVQYXRoKGNvbnRleHQsIGN1cnIsIFVOREVGLCBhcmdzLCB2YWx1ZVN0YWNrKV0gPSBuZXdWYWx1ZTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0ID0gY29udGV4dFtyZXNvbHZlUGF0aChjb250ZXh0LCBjdXJyLCBVTkRFRiwgYXJncywgdmFsdWVTdGFjayldO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIC8vIEZ1bmN0aW9ucyBhcmUgY2FsbGVkIHVzaW5nIGBjYWxsYCBvciBgYXBwbHlgLCBkZXBlbmRpbmcgb24gdGhlIHN0YXRlIG9mXG4gICAgICAgICAgICAgICAgLy8gdGhlIGFyZ3VtZW50cyB3aXRoaW4gdGhlICggKSBjb250YWluZXIuIEZ1bmN0aW9ucyBhcmUgZXhlY3V0ZWQgd2l0aCBcInRoaXNcIlxuICAgICAgICAgICAgICAgIC8vIHNldCB0byB0aGUgY29udGV4dCBpbW1lZGlhdGVseSBwcmlvciB0byB0aGUgZnVuY3Rpb24gaW4gdGhlIHN0YWNrLlxuICAgICAgICAgICAgICAgIC8vIEZvciBleGFtcGxlLCBcImEuYi5jLmZuKClcIiBpcyBlcXVpdmFsZW50IHRvIG9iai5hLmIuYy5mbi5jYWxsKG9iai5hLmIuYylcbiAgICAgICAgICAgICAgICBlbHNlIGlmIChjdXJyLmV4ZWMgPT09ICRDQUxMKXtcbiAgICAgICAgICAgICAgICAgICAgaWYgKGN1cnIuZG9FYWNoKXtcbiAgICAgICAgICAgICAgICAgICAgICAgIGlmICghQXJyYXkuaXNBcnJheSh2YWx1ZVN0YWNrW3ZhbHVlU3RhY2tMZW5ndGggLSAyXSkpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldHVybiB1bmRlZmluZWQ7XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICByZXQgPSBbXTtcbiAgICAgICAgICAgICAgICAgICAgICAgIGkgPSAwO1xuICAgICAgICAgICAgICAgICAgICAgICAgZWFjaExlbmd0aCA9IGNvbnRleHQubGVuZ3RoO1xuICAgICAgICAgICAgICAgICAgICAgICAgd2hpbGUoaSA8IGVhY2hMZW5ndGgpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIC8vIElmIGZ1bmN0aW9uIGNhbGwgaGFzIGFyZ3VtZW50cywgcHJvY2VzcyB0aG9zZSBhcmd1bWVudHMgYXMgYSBuZXcgcGF0aFxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLnQgJiYgY3Vyci50Lmxlbmd0aCl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNhbGxBcmdzID0gcmVzb2x2ZVBhdGgoY29udGV4dCwgY3VyciwgVU5ERUYsIGFyZ3MsIHZhbHVlU3RhY2spO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBpZiAoY2FsbEFyZ3MgPT09IFVOREVGKXtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIHJldC5wdXNoKGNvbnRleHRbaV0uYXBwbHkodmFsdWVTdGFja1t2YWx1ZVN0YWNrTGVuZ3RoIC0gMl1baV0pKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIGlmIChBcnJheS5pc0FycmF5KGNhbGxBcmdzKSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChjb250ZXh0W2ldLmFwcGx5KHZhbHVlU3RhY2tbdmFsdWVTdGFja0xlbmd0aCAtIDJdW2ldLCBjYWxsQXJncykpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgcmV0LnB1c2goY29udGV4dFtpXS5jYWxsKHZhbHVlU3RhY2tbdmFsdWVTdGFja0xlbmd0aCAtIDJdW2ldLCBjYWxsQXJncykpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQucHVzaChjb250ZXh0W2ldLmNhbGwodmFsdWVTdGFja1t2YWx1ZVN0YWNrTGVuZ3RoIC0gMl1baV0pKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgaSsrO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgLy8gSWYgZnVuY3Rpb24gY2FsbCBoYXMgYXJndW1lbnRzLCBwcm9jZXNzIHRob3NlIGFyZ3VtZW50cyBhcyBhIG5ldyBwYXRoXG4gICAgICAgICAgICAgICAgICAgICAgICBpZiAoY3Vyci50ICYmIGN1cnIudC5sZW5ndGgpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjdXJyLnNpbXBsZSl7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgIGNhbGxBcmdzID0gX3RoaXMuZ2V0KGNvbnRleHQsIGN1cnIpO1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgY2FsbEFyZ3MgPSByZXNvbHZlUGF0aChjb250ZXh0LCBjdXJyLCBVTkRFRiwgYXJncywgdmFsdWVTdGFjayk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGlmIChjYWxsQXJncyA9PT0gVU5ERUYpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQgPSBjb250ZXh0LmFwcGx5KHZhbHVlU3RhY2tbdmFsdWVTdGFja0xlbmd0aCAtIDJdKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgZWxzZSBpZiAoQXJyYXkuaXNBcnJheShjYWxsQXJncykpe1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQgPSBjb250ZXh0LmFwcGx5KHZhbHVlU3RhY2tbdmFsdWVTdGFja0xlbmd0aCAtIDJdLCBjYWxsQXJncyk7XG4gICAgICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQgPSBjb250ZXh0LmNhbGwodmFsdWVTdGFja1t2YWx1ZVN0YWNrTGVuZ3RoIC0gMl0sIGNhbGxBcmdzKTtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgICAgICAgICByZXQgPSBjb250ZXh0LmNhbGwodmFsdWVTdGFja1t2YWx1ZVN0YWNrTGVuZ3RoIC0gMl0pO1xuICAgICAgICAgICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgLy8gQWRkIHRoZSByZXR1cm4gdmFsdWUgdG8gdGhlIHN0YWNrIGluIGNhc2Ugd2UgbXVzdCBsb29wIGFnYWluLlxuICAgICAgICAgICAgLy8gUmVjdXJzaXZlIGNhbGxzIHBhc3MgdGhlIHNhbWUgdmFsdWVTdGFjayBhcnJheSBhcm91bmQsIGJ1dCB3ZSBkb24ndCB3YW50IHRvXG4gICAgICAgICAgICAvLyBwdXNoIGVudHJpZXMgb24gdGhlIHN0YWNrIGluc2lkZSBhIHJlY3Vyc2lvbiwgc28gaW5zdGVhZCB1c2UgZml4ZWQgYXJyYXlcbiAgICAgICAgICAgIC8vIGluZGV4IHJlZmVyZW5jZXMgYmFzZWQgb24gd2hhdCAqKnRoaXMqKiBleGVjdXRpb24ga25vd3MgdGhlIHZhbHVlU3RhY2tMZW5ndGhcbiAgICAgICAgICAgIC8vIHNob3VsZCBiZS4gVGhhdCB3YXksIGlmIGEgcmVjdXJzaW9uIGFkZHMgbmV3IGVsZW1lbnRzLCBhbmQgdGhlbiB3ZSBiYWNrIG91dCxcbiAgICAgICAgICAgIC8vIHRoaXMgY29udGV4dCB3aWxsIHJlbWVtYmVyIHRoZSBvbGQgc3RhY2sgbGVuZ3RoIGFuZCB3aWxsIG1lcmVseSBvdmVyd3JpdGVcbiAgICAgICAgICAgIC8vIHRob3NlIGFkZGVkIGVudHJpZXMsIGlnbm9yaW5nIHRoYXQgdGhleSB3ZXJlIHRoZXJlIGluIHRoZSBmaXJzdCBwbGFjZS5cbiAgICAgICAgICAgIHZhbHVlU3RhY2tbdmFsdWVTdGFja0xlbmd0aCsrXSA9IHJldDtcbiAgICAgICAgICAgIGNvbnRleHQgPSByZXQ7XG4gICAgICAgICAgICBwcmV2ID0gcmV0O1xuICAgICAgICAgICAgaWR4Kys7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIGNvbnRleHQ7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIFNpbXBsaWZpZWQgcGF0aCBldmFsdWF0aW9uIGhlYXZpbHkgb3B0aW1pemVkIGZvciBwZXJmb3JtYW5jZSB3aGVuXG4gICAgICogcHJvY2Vzc2luZyBwYXRocyB3aXRoIG9ubHkgcHJvcGVydHkgbmFtZXMgb3IgaW5kaWNlcyBhbmQgc2VwYXJhdG9ycy5cbiAgICAgKiBJZiB0aGUgcGF0aCBjYW4gYmUgY29ycmVjdGx5IHByb2Nlc3NlZCB3aXRoIFwicGF0aC5zcGxpdChzZXBhcmF0b3IpXCIsXG4gICAgICogdGhpcyBmdW5jdGlvbiB3aWxsIGRvIHNvLiBBbnkgb3RoZXIgc3BlY2lhbCBjaGFyYWN0ZXJzIGZvdW5kIGluIHRoZVxuICAgICAqIHBhdGggd2lsbCBjYXVzZSB0aGUgcGF0aCB0byBiZSBldmFsdWF0ZWQgd2l0aCB0aGUgZnVsbCBgcmVzb2x2ZVBhdGhgXG4gICAgICogZnVuY3Rpb24gaW5zdGVhZC5cbiAgICAgKiBAcHJpdmF0ZVxuICAgICAqIEBwYXJhbSAge09iamVjdH0gb2JqICAgICAgICBUaGUgZGF0YSBvYmplY3QgdG8gYmUgcmVhZC93cml0dGVuXG4gICAgICogQHBhcmFtICB7U3RyaW5nfSBwYXRoICAgICAgIFRoZSBrZXlwYXRoIHdoaWNoIGByZXNvbHZlUGF0aGAgd2lsbCBldmFsdWF0ZSBhZ2FpbnN0IGBvYmpgLlxuICAgICAqIEBwYXJhbSAge0FueX0gbmV3VmFsdWUgICBUaGUgbmV3IHZhbHVlIHRvIHNldCBhdCB0aGUgcG9pbnQgZGVzY3JpYmVkIGJ5IGBwYXRoYC4gVW5kZWZpbmVkIGlmIHVzZWQgaW4gYGdldGAgc2NlbmFyaW8uXG4gICAgICogQHJldHVybiB7QW55fSAgICAgICAgICAgIEluIGBnZXRgLCByZXR1cm5zIHRoZSB2YWx1ZSBmb3VuZCBpbiBgb2JqYCBhdCBgcGF0aGAuIEluIGBzZXRgLCByZXR1cm5zIHRoZSBuZXcgdmFsdWUgdGhhdCB3YXMgc2V0IGluIGBvYmpgLiBJZiBgZ2V0YCBvciBgc2V0YCBhcmUgbnRvIHN1Y2Nlc3NmdWwsIHJldHVybnMgYHVuZGVmaW5lZGBcbiAgICAgKi9cbiAgICB2YXIgcXVpY2tSZXNvbHZlU3RyaW5nID0gZnVuY3Rpb24ob2JqLCBwYXRoLCBuZXdWYWx1ZSl7XG4gICAgICAgIHZhciBjaGFuZ2UgPSBuZXdWYWx1ZSAhPT0gVU5ERUYsXG4gICAgICAgICAgICB0ayA9IFtdLFxuICAgICAgICAgICAgaSA9IDAsXG4gICAgICAgICAgICB0a0xlbmd0aCA9IDA7XG5cbiAgICAgICAgdGsgPSBwYXRoLnNwbGl0KHByb3BlcnR5U2VwYXJhdG9yKTtcbiAgICAgICAgb3B0LnVzZUNhY2hlICYmIChjYWNoZVtwYXRoXSA9IHt0OiB0aywgc2ltcGxlOiB0cnVlfSk7XG4gICAgICAgIHRrTGVuZ3RoID0gdGsubGVuZ3RoO1xuICAgICAgICB3aGlsZSAob2JqICE9PSBVTkRFRiAmJiBpIDwgdGtMZW5ndGgpe1xuICAgICAgICAgICAgaWYgKHRrW2ldID09PSAnJyl7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgICAgIGVsc2UgaWYgKGNoYW5nZSl7XG4gICAgICAgICAgICAgICAgaWYgKGkgPT09IHRrTGVuZ3RoIC0gMSl7XG4gICAgICAgICAgICAgICAgICAgIG9ialt0a1tpXV0gPSBuZXdWYWx1ZTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgLy8gRm9yIGFycmF5cywgdGVzdCBjdXJyZW50IGNvbnRleHQgYWdhaW5zdCB1bmRlZmluZWQgdG8gYXZvaWQgcGFyc2luZyB0aGlzIHNlZ21lbnQgYXMgYSBudW1iZXIuXG4gICAgICAgICAgICAgICAgLy8gRm9yIGFueXRoaW5nIGVsc2UsIHVzZSBoYXNPd25Qcm9wZXJ0eS5cbiAgICAgICAgICAgICAgICBlbHNlIGlmIChvcHQuZm9yY2UgJiYgdHlwZW9mIG9ialt0a1tpXV0gPT09ICd1bmRlZmluZWQnKSB7XG4gICAgICAgICAgICAgICAgICAgIG9ialt0a1tpXV0gPSB7fTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBvYmogPSBvYmpbdGtbaSsrXV07XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIG9iajtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogU2ltcGxpZmllZCBwYXRoIGV2YWx1YXRpb24gaGVhdmlseSBvcHRpbWl6ZWQgZm9yIHBlcmZvcm1hbmNlIHdoZW5cbiAgICAgKiBwcm9jZXNzaW5nIGFycmF5IG9mIHNpbXBsZSBwYXRoIHRva2VucyAocGxhaW4gcHJvcGVydHkgbmFtZXMpLlxuICAgICAqIFRoaXMgZnVuY3Rpb24gaXMgZXNzZW50aWFsbHkgdGhlIHNhbWUgYXMgYHF1aWNrUmVzb2x2ZVN0cmluZ2AgZXhjZXB0XG4gICAgICogYHF1aWNrUmVzb2x2ZVRva2VuQXJyYXlgIGRvZXMgbnRvIG5lZWQgdG8gZXhlY3V0ZSBwYXRoLnNwbGl0LlxuICAgICAqIEBwcml2YXRlXG4gICAgICogQHBhcmFtICB7T2JqZWN0fSBvYmogICAgICAgIFRoZSBkYXRhIG9iamVjdCB0byBiZSByZWFkL3dyaXR0ZW5cbiAgICAgKiBAcGFyYW0gIHtBcnJheX0gdGsgICAgICAgVGhlIHRva2VuIGFycmF5IHdoaWNoIGByZXNvbHZlUGF0aGAgd2lsbCBldmFsdWF0ZSBhZ2FpbnN0IGBvYmpgLlxuICAgICAqIEBwYXJhbSAge0FueX0gbmV3VmFsdWUgICBUaGUgbmV3IHZhbHVlIHRvIHNldCBhdCB0aGUgcG9pbnQgZGVzY3JpYmVkIGJ5IGBwYXRoYC4gVW5kZWZpbmVkIGlmIHVzZWQgaW4gYGdldGAgc2NlbmFyaW8uXG4gICAgICogQHJldHVybiB7QW55fSAgICAgICAgICAgIEluIGBnZXRgLCByZXR1cm5zIHRoZSB2YWx1ZSBmb3VuZCBpbiBgb2JqYCBhdCBgcGF0aGAuIEluIGBzZXRgLCByZXR1cm5zIHRoZSBuZXcgdmFsdWUgdGhhdCB3YXMgc2V0IGluIGBvYmpgLiBJZiBgZ2V0YCBvciBgc2V0YCBhcmUgbnRvIHN1Y2Nlc3NmdWwsIHJldHVybnMgYHVuZGVmaW5lZGBcbiAgICAgKi9cbiAgICB2YXIgcXVpY2tSZXNvbHZlVG9rZW5BcnJheSA9IGZ1bmN0aW9uKG9iaiwgdGssIG5ld1ZhbHVlKXtcbiAgICAgICAgdmFyIGNoYW5nZSA9IG5ld1ZhbHVlICE9PSBVTkRFRixcbiAgICAgICAgICAgIGkgPSAwLFxuICAgICAgICAgICAgdGtMZW5ndGggPSB0ay5sZW5ndGg7XG5cbiAgICAgICAgd2hpbGUgKG9iaiAhPSBudWxsICYmIGkgPCB0a0xlbmd0aCl7XG4gICAgICAgICAgICBpZiAodGtbaV0gPT09ICcnKXsgcmV0dXJuIHVuZGVmaW5lZDsgfVxuICAgICAgICAgICAgZWxzZSBpZiAoY2hhbmdlKXtcbiAgICAgICAgICAgICAgICBpZiAoaSA9PT0gdGtMZW5ndGggLSAxKXtcbiAgICAgICAgICAgICAgICAgICAgb2JqW3RrW2ldXSA9IG5ld1ZhbHVlO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICAvLyBGb3IgYXJyYXlzLCB0ZXN0IGN1cnJlbnQgY29udGV4dCBhZ2FpbnN0IHVuZGVmaW5lZCB0byBhdm9pZCBwYXJzaW5nIHRoaXMgc2VnbWVudCBhcyBhIG51bWJlci5cbiAgICAgICAgICAgICAgICAvLyBGb3IgYW55dGhpbmcgZWxzZSwgdXNlIGhhc093blByb3BlcnR5LlxuICAgICAgICAgICAgICAgIGVsc2UgaWYgKG9wdC5mb3JjZSAmJiB0eXBlb2Ygb2JqW3RrW2ldXSA9PT0gJ3VuZGVmaW5lZCcpIHtcbiAgICAgICAgICAgICAgICAgICAgb2JqW3RrW2ldXSA9IHt9O1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIG9iaiA9IG9ialt0a1tpKytdXTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gb2JqO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBTZWFyY2hlcyBhbiBvYmplY3Qgb3IgYXJyYXkgZm9yIGEgdmFsdWUsIGFjY3VtdWxhdGluZyB0aGUga2V5cGF0aCB0byB0aGUgdmFsdWUgYWxvbmdcbiAgICAgKiB0aGUgd2F5LiBPcGVyYXRlcyBpbiBhIHJlY3Vyc2l2ZSB3YXkgdW50aWwgZWl0aGVyIGFsbCBrZXlzL2luZGljZXMgaGF2ZSBiZWVuXG4gICAgICogZXhoYXVzdGVkIG9yIGEgbWF0Y2ggaXMgZm91bmQuIFJldHVybiB2YWx1ZSBcInRydWVcIiBtZWFucyBcImtlZXAgc2Nhbm5pbmdcIiwgXCJmYWxzZVwiXG4gICAgICogbWVhbnMgXCJzdG9wIG5vd1wiLiBJZiBhIG1hdGNoIGlzIGZvdW5kLCBpbnN0ZWFkIG9mIHJldHVybmluZyBhIHNpbXBsZSBcImZhbHNlXCIsIGFcbiAgICAgKiBjYWxsYmFjayBmdW5jdGlvbiAoc2F2ZVBhdGgpIGlzIGNhbGxlZCB3aGljaCB3aWxsIGRlY2lkZSB3aGV0aGVyIG9yIG5vdCB0byBjb250aW51ZVxuICAgICAqIHRoZSBzY2FuLiBUaGlzIGFsbG93cyB0aGUgZnVuY3Rpb24gdG8gZmluZCBvbmUgaW5zdGFuY2Ugb2YgdmFsdWUgb3IgYWxsIGluc3RhbmNlcyxcbiAgICAgKiBiYXNlZCBvbiBsb2dpYyBpbiB0aGUgY2FsbGJhY2suXG4gICAgICogQHByaXZhdGVcbiAgICAgKiBAcGFyYW0ge09iamVjdH0gb2JqICAgIFRoZSBkYXRhIG9iamVjdCB0byBzY2FuXG4gICAgICogQHBhcmFtIHtBbnl9IHZhbCBUaGUgdmFsdWUgd2UgYXJlIGxvb2tpbmcgZm9yIHdpdGhpbiBgb2JqYFxuICAgICAqIEBwYXJhbSB7RnVuY3Rpb259IHNhdmVQYXRoIENhbGxiYWNrIGZ1bmN0aW9uIHdoaWNoIHdpbGwgc3RvcmUgYWNjdW11bGF0ZWQgcGF0aHMgYW5kIGluZGljYXRlIHdoZXRoZXIgdG8gY29udGludWVcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gcGF0aCBBY2N1bXVsYXRlZCBrZXlwYXRoOyB1bmRlZmluZWQgYXQgZmlyc3QsIHBvcHVsYXRlZCBpbiByZWN1cnNpdmUgY2FsbHNcbiAgICAgKiBAcGFyYW0ge0Z1bmN0aW9ufSBpc0NpcmN1bGFyQ2IgQ2FsbGJhY2sgZnVuY3Rpb24gd2hpY2ggcmV0dXJuIHRydWUgaWYgdGhpcyBvYmplY3QgaGFzIGNpcmN1bGFyIGFuY2VzdHJ5LCB1c2VkIGJ5IGBmaW5kU2FmZSgpYFxuICAgICAqIEByZXR1cm4ge0Jvb2xlYW59IEluZGljYXRlcyB3aGV0aGVyIHNjYW4gcHJvY2VzcyBzaG91bGQgY29udGludWUgKFwidHJ1ZVwiLT55ZXMsIFwiZmFsc2VcIi0+bm8pXG4gICAgICovXG4gICAgdmFyIHNjYW5Gb3JWYWx1ZSA9IGZ1bmN0aW9uKG9iaiwgdmFsLCBzYXZlUGF0aCwgcGF0aCwgaXNDaXJjdWxhckNiKXtcbiAgICAgICAgdmFyIGksIGxlbiwgbW9yZSwga2V5cywgcHJvcDtcblxuICAgICAgICBwYXRoID0gcGF0aCA/IHBhdGggOiAnJztcblxuICAgICAgICBpZih0eXBlb2YgaXNDaXJjdWxhckNiICE9PSAkVU5ERUZJTkVEICYmIHBhdGgpe1xuICAgICAgICAgICAgaWYoaXNDaXJjdWxhckNiKG9iaiwgcGF0aCkpe1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignQ2lyY3VsYXIgb2JqZWN0IHByb3ZpZGVkLiBQYXRoIGF0IFwiJyArIHBhdGggKyAnXCIgbWFrZXMgYSBsb29wLicpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG5cbiAgICAgICAgLy8gSWYgd2UgZm91bmQgdGhlIHZhbHVlIHdlJ3JlIGxvb2tpbmcgZm9yXG4gICAgICAgIGlmIChvYmogPT09IHZhbCl7XG4gICAgICAgICAgICByZXR1cm4gc2F2ZVBhdGgocGF0aCk7IC8vIFNhdmUgdGhlIGFjY3VtdWxhdGVkIHBhdGgsIGFzayB3aGV0aGVyIHRvIGNvbnRpbnVlXG4gICAgICAgIH1cbiAgICAgICAgLy8gVGhpcyBvYmplY3QgaXMgYW4gYXJyYXksIHNvIGV4YW1pbmUgZWFjaCBpbmRleCBzZXBhcmF0ZWx5XG4gICAgICAgIGVsc2UgaWYgKEFycmF5LmlzQXJyYXkob2JqKSl7XG4gICAgICAgICAgICBsZW4gPSBvYmoubGVuZ3RoO1xuICAgICAgICAgICAgZm9yKGkgPSAwOyBpIDwgbGVuOyBpKyspe1xuICAgICAgICAgICAgICBtb3JlID0gc2NhbkZvclZhbHVlKG9ialtpXSwgdmFsLCBzYXZlUGF0aCwgcGF0aCA/IHBhdGggKyBwcm9wZXJ0eVNlcGFyYXRvciArIGkgOiBpLCBpc0NpcmN1bGFyQ2IpO1xuICAgICAgICAgICAgICAgIC8vIENhbGwgYHNjYW5Gb3JWYWx1ZWAgcmVjdXJzaXZlbHlcbiAgICAgICAgICAgICAgICAvLyBIYWx0IGlmIHRoYXQgcmVjdXJzaXZlIGNhbGwgcmV0dXJuZWQgXCJmYWxzZVwiXG4gICAgICAgICAgICAgICAgaWYgKCFtb3JlKXsgcmV0dXJuOyB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gdHJ1ZTsgLy8ga2VlcCBsb29raW5nXG4gICAgICAgIH1cbiAgICAgICAgLy8gVGhpcyBvYmplY3QgaXMgYW4gb2JqZWN0LCBzbyBleGFtaW5lIGVhY2ggbG9jYWwgcHJvcGVydHkgc2VwYXJhdGVseVxuICAgICAgICBlbHNlIGlmIChpc09iamVjdChvYmopKSB7XG4gICAgICAgICAgICBrZXlzID0gT2JqZWN0LmtleXMob2JqKTtcbiAgICAgICAgICAgIGxlbiA9IGtleXMubGVuZ3RoO1xuICAgICAgICAgICAgaWYgKGxlbiA+IDEpeyBrZXlzID0ga2V5cy5zb3J0KCk7IH0gLy8gRm9yY2Ugb3JkZXIgb2Ygb2JqZWN0IGtleXMgdG8gcHJvZHVjZSByZXBlYXRhYmxlIHJlc3VsdHNcbiAgICAgICAgICAgIGZvciAoaSA9IDA7IGkgPCBsZW47IGkrKyl7XG4gICAgICAgICAgICAgICAgaWYgKG9iai5oYXNPd25Qcm9wZXJ0eShrZXlzW2ldKSl7XG4gICAgICAgICAgICAgICAgICAgIHByb3AgPSBrZXlzW2ldO1xuICAgICAgICAgICAgICAgICAgICAvLyBQcm9wZXJ0eSBtYXkgaW5jbHVkZSB0aGUgc2VwYXJhdG9yIGNoYXJhY3RlciBvciBzb21lIG90aGVyIHNwZWNpYWwgY2hhcmFjdGVyLFxuICAgICAgICAgICAgICAgICAgICAvLyBzbyBxdW90ZSB0aGlzIHBhdGggc2VnbWVudCBhbmQgZXNjYXBlIGFueSBzZXBhcmF0b3JzIHdpdGhpbi5cbiAgICAgICAgICAgICAgICAgICAgaWYgKGFsbFNwZWNpYWxzUmVnRXgudGVzdChwcm9wKSl7XG4gICAgICAgICAgICAgICAgICAgICAgICBwcm9wID0gcXVvdGVTdHJpbmcoc2luZ2xlcXVvdGUsIHByb3ApO1xuICAgICAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgICAgIG1vcmUgPSBzY2FuRm9yVmFsdWUob2JqW2tleXNbaV1dLCB2YWwsIHNhdmVQYXRoLCBwYXRoID8gcGF0aCArIHByb3BlcnR5U2VwYXJhdG9yICsgcHJvcCA6IHByb3AsIGlzQ2lyY3VsYXJDYik7XG4gICAgICAgICAgICAgICAgICAgIGlmICghbW9yZSl7IHJldHVybjsgfVxuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVybiB0cnVlOyAvLyBrZWVwIGxvb2tpbmdcbiAgICAgICAgfVxuICAgICAgICAvLyBMZWFmIG5vZGUgKHN0cmluZywgbnVtYmVyLCBjaGFyYWN0ZXIsIGJvb2xlYW4sIGV0Yy4pLCBidXQgZGlkbid0IG1hdGNoXG4gICAgICAgIHJldHVybiB0cnVlOyAvLyBrZWVwIGxvb2tpbmdcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogR2V0IHRva2VuaXplZCByZXByZXNlbnRhdGlvbiBvZiBzdHJpbmcga2V5cGF0aC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHBhdGggS2V5cGF0aFxuICAgICAqIEByZXR1cm4ge09iamVjdH0gT2JqZWN0IGluY2x1ZGluZyB0aGUgYXJyYXkgb2YgcGF0aCB0b2tlbnMgYW5kIGEgYm9vbGVhbiBpbmRpY2F0aW5nIFwic2ltcGxlXCIuIFNpbXBsZSB0b2tlbiBzZXRzIGhhdmUgbm8gc3BlY2lhbCBvcGVyYXRvcnMgb3IgbmVzdGVkIHRva2Vucywgb25seSBhIHBsYWluIGFycmF5IG9mIHN0cmluZ3MgZm9yIGZhc3QgZXZhbHVhdGlvbi5cbiAgICAgKi9cbiAgICBfdGhpcy5nZXRUb2tlbnMgPSBmdW5jdGlvbihwYXRoKXtcbiAgICAgICAgdmFyIHRva2VucyA9IHRva2VuaXplKHBhdGgpO1xuICAgICAgICBpZiAodHlwZW9mIHRva2VucyA9PT0gJFVOREVGSU5FRCl7IHJldHVybiB1bmRlZmluZWQ7IH1cbiAgICAgICAgcmV0dXJuIHRva2VucztcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogSW5mb3JtcyB3aGV0aGVyIHRoZSBzdHJpbmcgcGF0aCBoYXMgdmFsaWQgc3ludGF4LiBUaGUgcGF0aCBpcyBOT1QgZXZhbHVhdGVkIGFnYWluc3QgYVxuICAgICAqIGRhdGEgb2JqZWN0LCBvbmx5IHRoZSBzeW50YXggaXMgY2hlY2tlZC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHBhdGggS2V5cGF0aFxuICAgICAqIEByZXR1cm4ge0Jvb2xlYW59IHZhbGlkIHN5bnRheCAtPiBcInRydWVcIjsgbm90IHZhbGlkIC0+IFwiZmFsc2VcIlxuICAgICAqL1xuICAgIF90aGlzLmlzVmFsaWQgPSBmdW5jdGlvbihwYXRoKXtcbiAgICAgICAgcmV0dXJuIHR5cGVvZiB0b2tlbml6ZShwYXRoKSAhPT0gJFVOREVGSU5FRDtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogRXNjYXBlcyBhbnkgc3BlY2lhbCBjaGFyYWN0ZXJzIGZvdW5kIGluIHRoZSBpbnB1dCBzdHJpbmcgdXNpbmcgYmFja3NsYXNoLCBwcmV2ZW50aW5nXG4gICAgICogdGhlc2UgY2hhcmFjdGVycyBmcm9tIGNhdXNpbmcgdW5pbnRlbmRlZCBwcm9jZXNzaW5nIGJ5IFBhdGhUb29sa2l0LiBUaGlzIGZ1bmN0aW9uXG4gICAgICogRE9FUyByZXNwZWN0IHRoZSBjdXJyZW50IGNvbmZpZ3VyZWQgc3ludGF4LCBldmVuIGlmIGl0IGhhcyBiZWVuIGFsdGVyZWQgZnJvbSB0aGUgZGVmYXVsdC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHNlZ21lbnQgU2VnbWVudCBvZiBhIGtleXBhdGhcbiAgICAgKiBAcmV0dXJuIHtTdHJpbmd9IFRoZSBvcmlnaW5hbCBzZWdtZW50IHN0cmluZyB3aXRoIGFsbCBQYXRoVG9vbGtpdCBzcGVjaWFsIGNoYXJhY3RlcnMgcHJlcGVuZGVkIHdpdGggXCJcXFwiXG4gICAgICovXG4gICAgX3RoaXMuZXNjYXBlID0gZnVuY3Rpb24oc2VnbWVudCl7XG4gICAgICAgIHJldHVybiBzZWdtZW50LnJlcGxhY2UoYWxsU3BlY2lhbHNSZWdFeCwgJ1xcXFwkJicpO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBFdmFsdWF0ZXMga2V5cGF0aCBpbiBvYmplY3QgYW5kIHJldHVybnMgdGhlIHZhbHVlIGZvdW5kIHRoZXJlLCBpZiBhdmFpbGFibGUuIElmIHRoZSBwYXRoXG4gICAgICogZG9lcyBub3QgZXhpc3QgaW4gdGhlIHByb3ZpZGVkIGRhdGEgb2JqZWN0LCByZXR1cm5zIGB1bmRlZmluZWRgICh0aGlzIHJldHVybiB2YWx1ZSBpc1xuICAgICAqIGNvbmZpZ3VyYWJsZSBpbiBvcHRpb25zLCBzZWUgYHNldERlZmF1bHRSZXR1cm5WYWxgIGJlbG93KS4gRm9yIFwic2ltcGxlXCIgcGF0aHMsIHdoaWNoXG4gICAgICogZG9uJ3QgaW5jbHVkZSBhbnkgb3BlcmF0aW9ucyBiZXlvbmQgcHJvcGVydHkgc2VwYXJhdG9ycywgb3B0aW1pemVkIHJlc29sdmVycyB3aWxsIGJlIHVzZWRcbiAgICAgKiB3aGljaCBhcmUgbW9yZSBsaWdodHdlaWdodCB0aGFuIHRoZSBmdWxsLWZlYXR1cmVkIGByZXNvbHZlUGF0aGAuXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7QW55fSBvYmogU291cmNlIGRhdGEgb2JqZWN0XG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHBhdGggS2V5cGF0aCB0byBldmFsdWF0ZSB3aXRoaW4gXCJvYmpcIi4gQWxzbyBhY2NlcHRzIHRva2VuIGFycmF5IGluIHBsYWNlIG9mIGEgc3RyaW5nIHBhdGguXG4gICAgICogQHJldHVybiB7QW55fSBJZiB0aGUga2V5cGF0aCBleGlzdHMgaW4gXCJvYmpcIiwgcmV0dXJuIHRoZSB2YWx1ZSBhdCB0aGF0IGxvY2F0aW9uOyBJZiBub3QsIHJldHVybiBgdW5kZWZpbmVkYC5cbiAgICAgKi9cbiAgICBfdGhpcy5nZXQgPSBmdW5jdGlvbiAob2JqLCBwYXRoKXtcbiAgICAgICAgdmFyIGkgPSAwLFxuICAgICAgICAgICAgcmV0dXJuVmFsLFxuICAgICAgICAgICAgbGVuID0gYXJndW1lbnRzLmxlbmd0aCxcbiAgICAgICAgICAgIGFyZ3M7XG4gICAgICAgIC8vIEZvciBzdHJpbmcgcGF0aHMsIGZpcnN0IHNlZSBpZiBwYXRoIGhhcyBhbHJlYWR5IGJlZW4gY2FjaGVkIGFuZCBpZiB0aGUgdG9rZW4gc2V0IGlzIHNpbXBsZS4gSWZcbiAgICAgICAgLy8gc28sIHdlIGNhbiB1c2UgdGhlIG9wdGltaXplZCB0b2tlbiBhcnJheSByZXNvbHZlciB1c2luZyB0aGUgY2FjaGVkIHRva2VuIHNldC5cbiAgICAgICAgLy8gSWYgdGhlcmUgaXMgbm8gY2FjaGVkIGVudHJ5LCB1c2UgUmVnRXggdG8gbG9vayBmb3Igc3BlY2lhbCBjaGFyYWN0ZXJzIGFwYXJ0IGZyb20gdGhlIHNlcGFyYXRvci5cbiAgICAgICAgLy8gSWYgbm9uZSBhcmUgZm91bmQsIHdlIGNhbiB1c2UgdGhlIG9wdGltaXplZCBzdHJpbmcgcmVzb2x2ZXIuXG4gICAgICAgIGlmICh0eXBlb2YgcGF0aCA9PT0gJFNUUklORyl7XG4gICAgICAgICAgICBpZiAob3B0LnVzZUNhY2hlICYmIGNhY2hlW3BhdGhdICYmIGNhY2hlW3BhdGhdLnNpbXBsZSl7XG4gICAgICAgICAgICAgICAgcmV0dXJuVmFsID0gcXVpY2tSZXNvbHZlVG9rZW5BcnJheShvYmosIGNhY2hlW3BhdGhdLnQpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSBpZiAoIXNpbXBsZVBhdGhSZWdFeC50ZXN0KHBhdGgpKXtcbiAgICAgICAgICAgICAgICByZXR1cm5WYWwgPSBxdWlja1Jlc29sdmVTdHJpbmcob2JqLCBwYXRoKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIC8vIElmIHdlIG1hZGUgaXQgdGhpcyBmYXIsIHRoZSBwYXRoIGlzIGNvbXBsZXggYW5kIG1heSBpbmNsdWRlIHBsYWNlaG9sZGVycy4gR2F0aGVyIHVwIGFueVxuICAgICAgICAgICAgLy8gZXh0cmEgYXJndW1lbnRzIGFuZCBjYWxsIHRoZSBmdWxsIGByZXNvbHZlUGF0aGAgZnVuY3Rpb24uXG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICBhcmdzID0gW107XG4gICAgICAgICAgICAgICAgaWYgKGxlbiA+IDIpe1xuICAgICAgICAgICAgICAgICAgICBmb3IgKGkgPSAyOyBpIDwgbGVuOyBpKyspIHsgYXJnc1tpLTJdID0gYXJndW1lbnRzW2ldOyB9XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIHJldHVyblZhbCA9IHJlc29sdmVQYXRoKG9iaiwgcGF0aCwgdW5kZWZpbmVkLCBhcmdzKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICAvLyBGb3IgYXJyYXkgcGF0aHMgKHByZS1jb21waWxlZCB0b2tlbiBzZXRzKSwgY2hlY2sgZm9yIHNpbXBsaWNpdHkgc28gd2UgY2FuIHVzZSB0aGUgb3B0aW1pemVkIHJlc29sdmVyLlxuICAgICAgICBlbHNlIGlmIChBcnJheS5pc0FycmF5KHBhdGgudCkgJiYgcGF0aC5zaW1wbGUpe1xuICAgICAgICAgICAgcmV0dXJuVmFsID0gcXVpY2tSZXNvbHZlVG9rZW5BcnJheShvYmosIHBhdGgudCk7XG4gICAgICAgIH1cbiAgICAgICAgLy8gSWYgd2UgbWFkZSBpdCB0aGlzIGZhciwgdGhlIHBhdGggaXMgY29tcGxleCBhbmQgbWF5IGluY2x1ZGUgcGxhY2Vob2xkZXJzLiBHYXRoZXIgdXAgYW55XG4gICAgICAgIC8vIGV4dHJhIGFyZ3VtZW50cyBhbmQgY2FsbCB0aGUgZnVsbCBgcmVzb2x2ZVBhdGhgIGZ1bmN0aW9uLlxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIGFyZ3MgPSBbXTtcbiAgICAgICAgICAgIGlmIChsZW4gPiAyKXtcbiAgICAgICAgICAgICAgICBmb3IgKGkgPSAyOyBpIDwgbGVuOyBpKyspIHsgYXJnc1tpLTJdID0gYXJndW1lbnRzW2ldOyB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm5WYWwgPSByZXNvbHZlUGF0aChvYmosIHBhdGgsIHVuZGVmaW5lZCwgYXJncyk7XG4gICAgICAgIH1cblxuICAgICAgICByZXR1cm4gcmV0dXJuVmFsID09PSBVTkRFRiA/IG9wdC5kZWZhdWx0UmV0dXJuVmFsIDogcmV0dXJuVmFsO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBFdmFsdWF0ZXMga2V5cGF0aCBpbiBvYmplY3QgYW5kIHJldHVybnMgdGhlIHZhbHVlIGZvdW5kIHRoZXJlLCBpZiBhdmFpbGFibGUuIElmIHRoZSBwYXRoXG4gICAgICogZG9lcyBub3QgZXhpc3QgaW4gdGhlIHByb3ZpZGVkIGRhdGEgb2JqZWN0LCByZXR1cm5zIGRlZmF1bHQgdmFsdWUgYXMgcHJvdmlkZWQgaW4gYXJndW1lbnRzLlxuICAgICAqIEZvciBcInNpbXBsZVwiIHBhdGhzLCB3aGljaCBkb24ndCBpbmNsdWRlIGFueSBvcGVyYXRpb25zIGJleW9uZCBwcm9wZXJ0eSBzZXBhcmF0b3JzLCBvcHRpbWl6ZWRcbiAgICAgKiByZXNvbHZlcnMgd2lsbCBiZSB1c2VkIHdoaWNoIGFyZSBtb3JlIGxpZ2h0d2VpZ2h0IHRoYW4gdGhlIGZ1bGwtZmVhdHVyZWQgYHJlc29sdmVQYXRoYC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtBbnl9IG9iaiBTb3VyY2UgZGF0YSBvYmplY3RcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gcGF0aCBLZXlwYXRoIHRvIGV2YWx1YXRlIHdpdGhpbiBcIm9ialwiLiBBbHNvIGFjY2VwdHMgdG9rZW4gYXJyYXkgaW4gcGxhY2Ugb2YgYSBzdHJpbmcgcGF0aC5cbiAgICAgKiBAcGFyYW0ge0FueX0gZGVmYXVsdFJldHVyblZhbCBWYWx1ZSB0byByZXR1cm4gaWYgXCJnZXRcIiByZXN1bHRzIGluIHVuZGVmaW5lZC5cbiAgICAgKiBAcmV0dXJuIHtBbnl9IElmIHRoZSBrZXlwYXRoIGV4aXN0cyBpbiBcIm9ialwiLCByZXR1cm4gdGhlIHZhbHVlIGF0IHRoYXQgbG9jYXRpb247IElmIG5vdCwgcmV0dXJuIHZhbHVlIGZyb20gXCJkZWZhdWx0UmV0dXJuVmFsXCIuXG4gICAgICovXG4gICAgX3RoaXMuZ2V0V2l0aERlZmF1bHQgPSBmdW5jdGlvbiAob2JqLCBwYXRoLCBkZWZhdWx0UmV0dXJuVmFsKXtcbiAgICAgICAgdmFyIGkgPSAwLFxuICAgICAgICAgICAgcmV0dXJuVmFsLFxuICAgICAgICAgICAgbGVuID0gYXJndW1lbnRzLmxlbmd0aCxcbiAgICAgICAgICAgIGFyZ3MgPSBbIG9iaiwgcGF0aCBdO1xuXG4gICAgICAgIC8vIENvZGUgYmVsb3cgZHVwbGljYXRlcyBcImdldFwiIG1ldGhvZCBhYm92ZSByYXRoZXIgdGhhbiBzaW1wbHkgZXhlY3V0aW5nIFwiZ2V0XCIgYW5kIGN1c3RvbWl6aW5nXG4gICAgICAgIC8vIHRoZSByZXR1cm4gdmFsdWUgYmVjYXVzZSBcImdldFwiIG1heSBoYXZlIGZhaWxlZCB0byByZXNvbHZlIGFuZCByZXR1cm5lZCBhIG5vbi11bmRlZmluZWQgdmFsdWVcbiAgICAgICAgLy8gZHVlIHRvIGFuIGluc3RhbmNlIG9wdGlvbiwgb3B0aW9ucy5kZWZhdWx0UmV0dXJuVmFsLiBJbiB0aGF0IGNhc2UsIHRoaXMgbWV0aG9kIGNhbid0IGtub3dcbiAgICAgICAgLy8gd2hldGhlciB0aGUgbm9uLXVuZGVmaW5lZCByZXR1cm4gdmFsdWUgd2FzIHRoZSBhY3R1YWwgdmFsdWUgYXQgdGhhdCBwYXRoLCBvciB3YXMgcmV0dXJuZWRcbiAgICAgICAgLy8gZHVlIHRvIHBhdGggcmVzb2x1dGlvbiBmYWlsdXJlLiBUbyBiZSBzYWZlLCB0aGVyZWZvcmUsIHRoZSBcImdldFwiIGxvZ2ljIGlzIGR1cGxpY2F0ZWQgYnV0XG4gICAgICAgIC8vIHRoZSBkZWZhdWx0UmV0dXJuVmFsIGFyZ3VtZW50IGlzIHVzZWQgaW4gcGxhY2Ugb2YgdGhlIGluc3RhbmNlIG9wdGlvbiBpbiBjYXNlIG9mIGZhaWx1cmUuXG5cbiAgICAgICAgLy8gRm9yIHN0cmluZyBwYXRocywgZmlyc3Qgc2VlIGlmIHBhdGggaGFzIGFscmVhZHkgYmVlbiBjYWNoZWQgYW5kIGlmIHRoZSB0b2tlbiBzZXQgaXMgc2ltcGxlLiBJZlxuICAgICAgICAvLyBzbywgd2UgY2FuIHVzZSB0aGUgb3B0aW1pemVkIHRva2VuIGFycmF5IHJlc29sdmVyIHVzaW5nIHRoZSBjYWNoZWQgdG9rZW4gc2V0LlxuICAgICAgICAvLyBJZiB0aGVyZSBpcyBubyBjYWNoZWQgZW50cnksIHVzZSBSZWdFeCB0byBsb29rIGZvciBzcGVjaWFsIGNoYXJhY3RlcnMgYXBhcnQgZnJvbSB0aGUgc2VwYXJhdG9yLlxuICAgICAgICAvLyBJZiBub25lIGFyZSBmb3VuZCwgd2UgY2FuIHVzZSB0aGUgb3B0aW1pemVkIHN0cmluZyByZXNvbHZlci5cbiAgICAgICAgaWYgKHR5cGVvZiBwYXRoID09PSAkU1RSSU5HKXtcbiAgICAgICAgICAgIGlmIChvcHQudXNlQ2FjaGUgJiYgY2FjaGVbcGF0aF0gJiYgY2FjaGVbcGF0aF0uc2ltcGxlKXtcbiAgICAgICAgICAgICAgICByZXR1cm5WYWwgPSBxdWlja1Jlc29sdmVUb2tlbkFycmF5KG9iaiwgY2FjaGVbcGF0aF0udCk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIGlmICghc2ltcGxlUGF0aFJlZ0V4LnRlc3QocGF0aCkpe1xuICAgICAgICAgICAgICAgIHJldHVyblZhbCA9IHF1aWNrUmVzb2x2ZVN0cmluZyhvYmosIHBhdGgpO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgLy8gSWYgd2UgbWFkZSBpdCB0aGlzIGZhciwgdGhlIHBhdGggaXMgY29tcGxleCBhbmQgbWF5IGluY2x1ZGUgcGxhY2Vob2xkZXJzLiBHYXRoZXIgdXAgYW55XG4gICAgICAgICAgICAvLyBleHRyYSBhcmd1bWVudHMgYW5kIGNhbGwgdGhlIGZ1bGwgYHJlc29sdmVQYXRoYCBmdW5jdGlvbi5cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIGFyZ3MgPSBbXTtcbiAgICAgICAgICAgICAgICBpZiAobGVuID4gMyl7XG4gICAgICAgICAgICAgICAgICAgIGZvciAoaSA9IDM7IGkgPCBsZW47IGkrKykgeyBhcmdzW2ktM10gPSBhcmd1bWVudHNbaV07IH1cbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgcmV0dXJuVmFsID0gcmVzb2x2ZVBhdGgob2JqLCBwYXRoLCB1bmRlZmluZWQsIGFyZ3MpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIC8vIEZvciBhcnJheSBwYXRocyAocHJlLWNvbXBpbGVkIHRva2VuIHNldHMpLCBjaGVjayBmb3Igc2ltcGxpY2l0eSBzbyB3ZSBjYW4gdXNlIHRoZSBvcHRpbWl6ZWQgcmVzb2x2ZXIuXG4gICAgICAgIGVsc2UgaWYgKEFycmF5LmlzQXJyYXkocGF0aC50KSAmJiBwYXRoLnNpbXBsZSl7XG4gICAgICAgICAgICByZXR1cm5WYWwgPSBxdWlja1Jlc29sdmVUb2tlbkFycmF5KG9iaiwgcGF0aC50KTtcbiAgICAgICAgfVxuICAgICAgICAvLyBJZiB3ZSBtYWRlIGl0IHRoaXMgZmFyLCB0aGUgcGF0aCBpcyBjb21wbGV4IGFuZCBtYXkgaW5jbHVkZSBwbGFjZWhvbGRlcnMuIEdhdGhlciB1cCBhbnlcbiAgICAgICAgLy8gZXh0cmEgYXJndW1lbnRzIGFuZCBjYWxsIHRoZSBmdWxsIGByZXNvbHZlUGF0aGAgZnVuY3Rpb24uXG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgYXJncyA9IFtdO1xuICAgICAgICAgICAgaWYgKGxlbiA+IDMpe1xuICAgICAgICAgICAgICAgIGZvciAoaSA9IDM7IGkgPCBsZW47IGkrKykgeyBhcmdzW2ktM10gPSBhcmd1bWVudHNbaV07IH1cbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIHJldHVyblZhbCA9IHJlc29sdmVQYXRoKG9iaiwgcGF0aCwgdW5kZWZpbmVkLCBhcmdzKTtcbiAgICAgICAgfVxuXG4gICAgICAgIHJldHVybiByZXR1cm5WYWwgPT09IFVOREVGID8gZGVmYXVsdFJldHVyblZhbCA6IHJldHVyblZhbDtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogRXZhbHVhdGVzIGEga2V5cGF0aCBpbiBvYmplY3QgYW5kIHNldHMgYSBuZXcgdmFsdWUgYXQgdGhlIHBvaW50IGRlc2NyaWJlZCBpbiB0aGUga2V5cGF0aC4gSWZcbiAgICAgKiBcImZvcmNlXCIgaXMgZGlzYWJsZWQsIHRoZSBmdWxsIHBhdGggbXVzdCBleGlzdCB1cCB0byB0aGUgZmluYWwgcHJvcGVydHksIHdoaWNoIG1heSBiZSBjcmVhdGVkXG4gICAgICogYnkgdGhlIHNldCBvcGVyYXRpb24uIElmIFwiZm9yY2VcIiBpcyBlbmFibGVkLCBhbnkgbWlzc2luZyBpbnRlcm1lZGlhdGUgcHJvcGVydGllcyB3aWxsIGJlIGNyZWF0ZWRcbiAgICAgKiBpbiBvcmRlciB0byBzZXQgdGhlIHZhbHVlIG9uIHRoZSBmaW5hbCBwcm9wZXJ0eS4gSWYgYHNldGAgc3VjY2VlZHMsIHJldHVybnMgXCJ0cnVlXCIsIG90aGVyd2lzZSBcImZhbHNlXCIuXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7QW55fSBvYmogU291cmNlIGRhdGEgb2JqZWN0XG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHBhdGggS2V5cGF0aCB0byBldmFsdWF0ZSB3aXRoaW4gXCJvYmpcIi4gQWxzbyBhY2NlcHRzIHRva2VuIGFycmF5IGluIHBsYWNlIG9mIGEgc3RyaW5nIHBhdGguXG4gICAgICogQHBhcmFtIHtBbnl9IHZhbCBOZXcgdmFsdWUgdG8gc2V0IGF0IHRoZSBsb2NhdGlvbiBkZXNjcmliZWQgaW4gXCJwYXRoXCJcbiAgICAgKiBAcmV0dXJuIHtCb29sZWFufSBcInRydWVcIiBpZiB0aGUgc2V0IG9wZXJhdGlvbiBzdWNjZWVkczsgXCJmYWxzZVwiIGlmIGl0IGRvZXMgbm90IHN1Y2NlZWRcbiAgICAgKi9cbiAgICBfdGhpcy5zZXQgPSBmdW5jdGlvbihvYmosIHBhdGgsIHZhbCl7XG4gICAgICAgIHZhciBpID0gMCxcbiAgICAgICAgICAgIGxlbiA9IGFyZ3VtZW50cy5sZW5ndGgsXG4gICAgICAgICAgICBhcmdzLFxuICAgICAgICAgICAgcmVmLFxuICAgICAgICAgICAgZG9uZSA9IGZhbHNlO1xuXG4gICAgICAgIC8vIFBhdGggcmVzb2x1dGlvbiBmb2xsb3dzIHRoZSBzYW1lIGxvZ2ljIGFzIGBnZXRgIGFib3ZlLCB3aXRoIG9uZSBkaWZmZXJlbmNlOiBgZ2V0YCB3aWxsXG4gICAgICAgIC8vIGFib3J0IGJ5IHJldHVybmluZyB0aGUgdmFsdWUgYXMgc29vbiBhcyBpdCdzIGZvdW5kLiBgc2V0YCBkb2VzIG5vdCBhYm9ydCBzbyB0aGUgaWYtZWxzZVxuICAgICAgICAvLyBzdHJ1Y3R1cmUgaXMgc2xpZ2h0bHkgZGlmZmVyZW50IHRvIGRpY3RhdGUgd2hlbi9pZiB0aGUgZmluYWwgY2FzZSBzaG91bGQgZXhlY3V0ZS5cbiAgICAgICAgaWYgKHR5cGVvZiBwYXRoID09PSAkU1RSSU5HKXtcbiAgICAgICAgICAgIGlmIChvcHQudXNlQ2FjaGUgJiYgY2FjaGVbcGF0aF0gJiYgY2FjaGVbcGF0aF0uc2ltcGxlKXtcbiAgICAgICAgICAgICAgICByZWYgPSBxdWlja1Jlc29sdmVUb2tlbkFycmF5KG9iaiwgY2FjaGVbcGF0aF0udCwgdmFsKTtcbiAgICAgICAgICAgICAgICBkb25lIHw9IHRydWU7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIGlmICghc2ltcGxlUGF0aFJlZ0V4LnRlc3QocGF0aCkpe1xuICAgICAgICAgICAgICAgIHJlZiA9IHF1aWNrUmVzb2x2ZVN0cmluZyhvYmosIHBhdGgsIHZhbCk7XG4gICAgICAgICAgICAgICAgZG9uZSB8PSB0cnVlO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2UgaWYgKEFycmF5LmlzQXJyYXkocGF0aC50KSAmJiBwYXRoLnNpbXBsZSl7XG4gICAgICAgICAgICByZWYgPSBxdWlja1Jlc29sdmVUb2tlbkFycmF5KG9iaiwgcGF0aC50LCB2YWwpO1xuICAgICAgICAgICAgZG9uZSB8PSB0cnVlO1xuICAgICAgICB9XG5cbiAgICAgICAgLy8gUGF0aCB3YXMgKHByb2JhYmx5KSBhIHN0cmluZyBhbmQgaXQgY29udGFpbmVkIGNvbXBsZXggcGF0aCBjaGFyYWN0ZXJzXG4gICAgICAgIGlmICghZG9uZSkge1xuICAgICAgICAgICAgaWYgKGxlbiA+IDMpe1xuICAgICAgICAgICAgICAgIGFyZ3MgPSBbXTtcbiAgICAgICAgICAgICAgICBmb3IgKGkgPSAzOyBpIDwgbGVuOyBpKyspIHsgYXJnc1tpLTNdID0gYXJndW1lbnRzW2ldOyB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZWYgPSByZXNvbHZlUGF0aChvYmosIHBhdGgsIHZhbCwgYXJncyk7XG4gICAgICAgIH1cblxuICAgICAgICAvLyBgc2V0YCBjYW4gc2V0IGEgbmV3IHZhbHVlIGluIG11bHRpcGxlIHBsYWNlcyBpZiB0aGUgZmluYWwgcGF0aCBzZWdtZW50IGlzIGFuIGFycmF5LlxuICAgICAgICAvLyBJZiBhbnkgb2YgdGhvc2UgdmFsdWUgYXNzaWdubWVudHMgZmFpbCwgYHNldGAgd2lsbCByZXR1cm4gXCJmYWxzZVwiIGluZGljYXRpbmcgZmFpbHVyZS5cbiAgICAgICAgaWYgKEFycmF5LmlzQXJyYXkocmVmKSl7XG4gICAgICAgICAgICByZXR1cm4gcmVmLmluZGV4T2YodW5kZWZpbmVkKSA9PT0gLTE7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHJlZiAhPT0gVU5ERUY7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIExvY2F0ZSBhIHZhbHVlIHdpdGhpbiBhbiBvYmplY3Qgb3IgYXJyYXkuIFRoaXMgaXMgdGhlIHB1YmxpY2x5IGV4cG9zZWQgaW50ZXJmYWNlIHRvIHRoZVxuICAgICAqIHByaXZhdGUgYHNjYW5Gb3JWYWx1ZWAgZnVuY3Rpb24gZGVmaW5lZCBhYm92ZS5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtBbnl9IG9iaiBTb3VyY2UgZGF0YSBvYmplY3RcbiAgICAgKiBAcGFyYW0ge0FueX0gdmFsIFRoZSB2YWx1ZSB0byBzZWFyY2ggZm9yIHdpdGhpbiBcIm9ialwiXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IG9uZU9yTWFueSBPcHRpb25hbDsgSWYgbWlzc2luZyBvciBcIm9uZVwiLCBgZmluZGAgd2lsbCBvbmx5IHJldHVybiB0aGUgZmlyc3QgdmFsaWQgcGF0aC4gSWYgXCJvbk9yTWFueVwiIGlzIGFueSBvdGhlciBzdHJpbmcsIGBmaW5kYCB3aWxsIHNjYW4gdGhlIGZ1bGwgb2JqZWN0IGxvb2tpbmcgZm9yIGFsbCB2YWxpZCBwYXRocyB0byBhbGwgY2FzZXMgd2hlcmUgXCJ2YWxcIiBhcHBlYXJzLlxuICAgICAqIEByZXR1cm4ge0FycmF5fSBBcnJheSBvZiBrZXlwYXRocyB0byBcInZhbFwiIG9yIGB1bmRlZmluZWRgIGlmIFwidmFsXCIgaXMgbm90IGZvdW5kLlxuICAgICAqL1xuICAgIF90aGlzLmZpbmQgPSBmdW5jdGlvbihvYmosIHZhbCwgb25lT3JNYW55KXtcbiAgICAgICAgdmFyIGZvdW5kUGF0aHMgPSBbXTtcbiAgICAgICAgLy8gc2F2ZVBhdGggaXMgdGhlIGNhbGxiYWNrIHdoaWNoIHdpbGwgYWNjdW11bGF0ZSBhbnkgZm91bmQgcGF0aHMgaW4gYSBsb2NhbCBhcnJheVxuICAgICAgICB2YXIgc2F2ZVBhdGggPSBmdW5jdGlvbihwYXRoKXtcbiAgICAgICAgICAgIGZvdW5kUGF0aHMucHVzaChwYXRoKTtcbiAgICAgICAgICAgIGlmKCFvbmVPck1hbnkgfHwgb25lT3JNYW55ID09PSAnb25lJyl7XG4gICAgICAgICAgICAgICAgcmV0dXJuIGZhbHNlOyAvLyBzdG9wIHNjYW5uaW5nIGZvciB2YWx1ZVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHRydWU7IC8vIGtlZXAgc2Nhbm5pbmcgZm9yIHZhbHVlIGVsc2V3aGVyZSBpbiBvYmplY3RcbiAgICAgICAgfTtcbiAgICAgICAgc2NhbkZvclZhbHVlKG9iaiwgdmFsLCBzYXZlUGF0aCk7XG4gICAgICAgIGlmKCFvbmVPck1hbnkgfHwgb25lT3JNYW55ID09PSAnb25lJyl7XG4gICAgICAgICAgICByZXR1cm4gZm91bmRQYXRocy5sZW5ndGggPiAwID8gZm91bmRQYXRoc1swXSA6IHVuZGVmaW5lZDtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gZm91bmRQYXRocy5sZW5ndGggPiAwID8gZm91bmRQYXRocyA6IHVuZGVmaW5lZDtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogTG9jYXRlIGEgdmFsdWUgd2l0aGluIGFuIG9iamVjdCBvciBhcnJheS4gRHVyaW5nIHNjYW4sIHByb3RlY3QgYWdhaW5zdCBsb29wIHJlZmVyZW5jZXMuXG4gICAgICogVGhpcyBpcyB0aGUgcHVibGljbHkgZXhwb3NlZCBpbnRlcmZhY2UgdG8gdGhlIHByaXZhdGUgYHNjYW5Gb3JWYWx1ZWAgZnVuY3Rpb24gZGVmaW5lZCBhYm92ZS5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtBbnl9IG9iaiBTb3VyY2UgZGF0YSBvYmplY3RcbiAgICAgKiBAcGFyYW0ge0FueX0gdmFsIFRoZSB2YWx1ZSB0byBzZWFyY2ggZm9yIHdpdGhpbiBcIm9ialwiXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IG9uZU9yTWFueSBPcHRpb25hbDsgSWYgbWlzc2luZyBvciBcIm9uZVwiLCBgZmluZGAgd2lsbCBvbmx5IHJldHVybiB0aGUgZmlyc3QgdmFsaWQgcGF0aC4gSWYgXCJvbk9yTWFueVwiIGlzIGFueSBvdGhlciBzdHJpbmcsIGBmaW5kYCB3aWxsIHNjYW4gdGhlIGZ1bGwgb2JqZWN0IGxvb2tpbmcgZm9yIGFsbCB2YWxpZCBwYXRocyB0byBhbGwgY2FzZXMgd2hlcmUgXCJ2YWxcIiBhcHBlYXJzLlxuICAgICAqIEByZXR1cm4ge0FycmF5fSBBcnJheSBvZiBrZXlwYXRocyB0byBcInZhbFwiIG9yIGB1bmRlZmluZWRgIGlmIFwidmFsXCIgaXMgbm90IGZvdW5kLlxuICAgICAqL1xuICAgIF90aGlzLmZpbmRTYWZlID0gZnVuY3Rpb24ob2JqLCB2YWwsIG9uZU9yTWFueSl7XG4gICAgICAgIHZhciBmb3VuZFBhdGhzID0gW107XG4gICAgICAgIC8vIHNhdmVQYXRoIGlzIHRoZSBjYWxsYmFjayB3aGljaCB3aWxsIGFjY3VtdWxhdGUgYW55IGZvdW5kIHBhdGhzIGluIGEgbG9jYWwgYXJyYXlcbiAgICAgICAgLy8gdmFyaWFibGUuXG4gICAgICAgIHZhciBzYXZlUGF0aCA9IGZ1bmN0aW9uKHBhdGgpe1xuICAgICAgICAgICAgZm91bmRQYXRocy5wdXNoKHBhdGgpO1xuICAgICAgICAgICAgaWYoIW9uZU9yTWFueSB8fCBvbmVPck1hbnkgPT09ICdvbmUnKXtcbiAgICAgICAgICAgICAgICByZXR1cm4gZmFsc2U7IC8vIHN0b3Agc2Nhbm5pbmcgZm9yIHZhbHVlXG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gdHJ1ZTsgLy8ga2VlcCBzY2FubmluZyBmb3IgdmFsdWUgZWxzZXdoZXJlIGluIG9iamVjdFxuICAgICAgICB9O1xuICAgICAgICAvLyBpc0NpcmN1bGFyIGlzIGEgY2FsbGJhY2sgdGhhdCB3aWxsIHRlc3QgaWYgdGhpcyBvYmplY3QgYWxzbyBleGlzdHNcbiAgICAgICAgLy8gaW4gYW4gYW5jZXN0b3IgcGF0aCwgaW5kaWNhdGluZyBhIGNpcmN1bGFyIHJlZmVyZW5jZS5cbiAgICAgICAgdmFyIGlzQ2lyY3VsYXIgPSBmdW5jdGlvbihyZWYsIHBhdGgpe1xuICAgICAgICAgICAgdmFyIHRva2VucyA9IF90aGlzLmdldFRva2VucyhwYXRoKTtcbiAgICAgICAgICAgIC8vIFdhbGsgdXAgdGhlIGFuY2VzdG9yIGNoYWluIGNoZWNraW5nIGZvciBlcXVhbGl0eSB3aXRoIGN1cnJlbnQgb2JqZWN0XG4gICAgICAgICAgICB3aGlsZSh0b2tlbnMudC5wb3AoKSl7XG4gICAgICAgICAgICAgICAgaWYoX3RoaXMuZ2V0KG9iaiwgdG9rZW5zKSA9PT0gcmVmKXtcbiAgICAgICAgICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIGZhbHNlO1xuICAgICAgICB9O1xuICAgICAgICBzY2FuRm9yVmFsdWUob2JqLCB2YWwsIHNhdmVQYXRoLCBVTkRFRiwgaXNDaXJjdWxhcik7XG4gICAgICAgIGlmKCFvbmVPck1hbnkgfHwgb25lT3JNYW55ID09PSAnb25lJyl7XG4gICAgICAgICAgICByZXR1cm4gZm91bmRQYXRocy5sZW5ndGggPiAwID8gZm91bmRQYXRoc1swXSA6IHVuZGVmaW5lZDtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gZm91bmRQYXRocy5sZW5ndGggPiAwID8gZm91bmRQYXRocyA6IHVuZGVmaW5lZDtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogRm9yIGEgZ2l2ZW4gc3BlY2lhbCBjaGFyYWN0ZXIgZ3JvdXAgKGUuZy4sIHNlcGFyYXRvcnMpIGFuZCBjaGFyYWN0ZXIgdHlwZSAoZS5nLiwgXCJwcm9wZXJ0eVwiKSxcbiAgICAgKiByZXBsYWNlIGFuIGV4aXN0aW5nIHNlcGFyYXRvciB3aXRoIGEgbmV3IGNoYXJhY3Rlci4gVGhpcyBjcmVhdGVzIGEgbmV3IHNwZWNpYWwgY2hhcmFjdGVyIGZvclxuICAgICAqIHRoYXQgcHVycG9zZSBhbndpdGhpbiB0aGUgY2hhcmFjdGVyIGdyb3VwIGFuZCByZW1vdmVzIHRoZSBvbGQgb25lLiBBbHNvIHRha2VzIGEgXCJjbG9zZXJcIiBhcmd1bWVudFxuICAgICAqIGZvciBjYXNlcyB3aGVyZSB0aGUgc3BlY2lhbCBjaGFyYWN0ZXIgaXMgYSBjb250YWluZXIgc2V0LlxuICAgICAqIEBwcml2YXRlXG4gICAgICogQHBhcmFtIHtPYmplY3R9IG9wdGlvbkdyb3VwIFJlZmVyZW5jZSB0byBjdXJyZW50IGNvbmZpZ3VyYXRpb24gZm9yIGEgY2VydGFpbiB0eXBlIG9mIHNwZWNpYWwgY2hhcmFjdGVyc1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBjaGFyVHlwZSBUaGUgdHlwZSBvZiBzcGVjaWFsIGNoYXJhY3RlciB0byBiZSByZXBsYWNlZFxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSB2YWwgTmV3IHNwZWNpYWwgY2hhcmFjdGVyIHN0cmluZ1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBjbG9zZXIgT3B0aW9uYWw7IE5ldyBzcGVjaWFsIGNoYXJhY3RlciBjbG9zZXIgc3RyaW5nLCBvbmx5IHVzZWQgZm9yIFwiY29udGFpbmVyc1wiIGdyb3VwXG4gICAgICovXG4gICAgdmFyIHVwZGF0ZU9wdGlvbkNoYXIgPSBmdW5jdGlvbihvcHRpb25Hcm91cCwgY2hhclR5cGUsIHZhbCwgY2xvc2VyKXtcbiAgICAgICAgdmFyIG9sZFZhbCA9ICcnO1xuICAgICAgICBPYmplY3Qua2V5cyhvcHRpb25Hcm91cCkuZm9yRWFjaChmdW5jdGlvbihzdHIpeyBpZiAob3B0aW9uR3JvdXBbc3RyXS5leGVjID09PSBjaGFyVHlwZSl7IG9sZFZhbCA9IHN0cjsgfSB9KTtcblxuICAgICAgICBkZWxldGUgb3B0aW9uR3JvdXBbb2xkVmFsXTtcbiAgICAgICAgb3B0aW9uR3JvdXBbdmFsXSA9IHtleGVjOiBjaGFyVHlwZX07XG4gICAgICAgIGlmIChjbG9zZXIpeyBvcHRpb25Hcm91cFt2YWxdLmNsb3NlciA9IGNsb3NlcjsgfVxuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBTZXRzIFwic2ltcGxlXCIgc3ludGF4IGluIHNwZWNpYWwgY2hhcmFjdGVyIGdyb3Vwcy4gVGhpcyBzeW50YXggb25seSBzdXBwb3J0cyBhIHNlcGFyYXRvclxuICAgICAqIGNoYXJhY3RlciBhbmQgbm8gb3RoZXIgb3BlcmF0b3JzLiBBIGN1c3RvbSBzZXBhcmF0b3IgbWF5IGJlIHByb3ZpZGVkIGFzIGFuIGFyZ3VtZW50LlxuICAgICAqIEBwcml2YXRlXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHNlcCBPcHRpb25hbDsgU2VwYXJhdG9yIHN0cmluZy4gSWYgbWlzc2luZywgdGhlIGRlZmF1bHQgc2VwYXJhdG9yIChcIi5cIikgaXMgdXNlZC5cbiAgICAgKi9cbiAgICB2YXIgc2V0U2ltcGxlT3B0aW9ucyA9IGZ1bmN0aW9uKHNlcCl7XG4gICAgICAgIHZhciBzZXBPcHRzID0ge307XG4gICAgICAgIGlmICghKHR5cGVvZiBzZXAgPT09ICRTVFJJTkcgJiYgc2VwLmxlbmd0aCA9PT0gMSkpe1xuICAgICAgICAgICAgc2VwID0gJy4nO1xuICAgICAgICB9XG4gICAgICAgIHNlcE9wdHNbc2VwXSA9IHtleGVjOiAkUFJPUEVSVFl9O1xuICAgICAgICBvcHQucHJlZml4ZXMgPSB7fTtcbiAgICAgICAgb3B0LmNvbnRhaW5lcnMgPSB7fTtcbiAgICAgICAgb3B0LnNlcGFyYXRvcnMgPSBzZXBPcHRzO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBBbHRlciBQYXRoVG9vbGtpdCBjb25maWd1cmF0aW9uLiBUYWtlcyBhbiBvcHRpb25zIGhhc2ggd2hpY2ggbWF5IGluY2x1ZGVcbiAgICAgKiBtdWx0aXBsZSBzZXR0aW5ncyB0byBjaGFuZ2UgYXQgb25jZS4gSWYgdGhlIHBhdGggc3ludGF4IGlzIGNoYW5nZWQgYnlcbiAgICAgKiBjaGFuZ2luZyBzcGVjaWFsIGNoYXJhY3RlcnMsIHRoZSBjYWNoZSBpcyB3aXBlZC4gRWFjaCBvcHRpb24gZ3JvdXAgaXNcbiAgICAgKiBSRVBMQUNFRCBieSB0aGUgbmV3IG9wdGlvbiBncm91cCBwYXNzZWQgaW4uIElmIGFuIG9wdGlvbiBncm91cCBpcyBub3RcbiAgICAgKiBpbmNsdWRlZCBpbiB0aGUgb3B0aW9ucyBoYXNoLCBpdCBpcyBub3QgY2hhbmdlZC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtPYmplY3R9IG9wdGlvbnMgT3B0aW9uIGhhc2guIEZvciBzYW1wbGUgaW5wdXQsIHNlZSBgc2V0RGVmYXVsdE9wdGlvbnNgIGFib3ZlLlxuICAgICAqL1xuICAgIF90aGlzLnNldE9wdGlvbnMgPSBmdW5jdGlvbihvcHRpb25zKXtcbiAgICAgICAgaWYgKG9wdGlvbnMucHJlZml4ZXMpe1xuICAgICAgICAgICAgb3B0LnByZWZpeGVzID0gb3B0aW9ucy5wcmVmaXhlcztcbiAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG9wdGlvbnMuc2VwYXJhdG9ycyl7XG4gICAgICAgICAgICBvcHQuc2VwYXJhdG9ycyA9IG9wdGlvbnMuc2VwYXJhdG9ycztcbiAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgIH1cbiAgICAgICAgaWYgKG9wdGlvbnMuY29udGFpbmVycyl7XG4gICAgICAgICAgICBvcHQuY29udGFpbmVycyA9IG9wdGlvbnMuY29udGFpbmVycztcbiAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgIH1cbiAgICAgICAgaWYgKHR5cGVvZiBvcHRpb25zLmNhY2hlICE9PSAkVU5ERUZJTkVEKXtcbiAgICAgICAgICAgIG9wdC51c2VDYWNoZSA9ICEhb3B0aW9ucy5jYWNoZTtcbiAgICAgICAgfVxuICAgICAgICBpZiAodHlwZW9mIG9wdGlvbnMuc2ltcGxlICE9PSAkVU5ERUZJTkVEKXtcbiAgICAgICAgICAgIHZhciB0ZW1wQ2FjaGUgPSBvcHQudXNlQ2FjaGU7IC8vIHByZXNlcnZlIHRoZXNlIHR3byBvcHRpb25zIGFmdGVyIFwic2V0RGVmYXVsdE9wdGlvbnNcIlxuICAgICAgICAgICAgdmFyIHRlbXBGb3JjZSA9IG9wdC5mb3JjZTtcbiAgICAgICAgICAgIHZhciB0ZW1wRGVmYXVsdFJldHVyblZhbCA9IG9wdC5kZWZhdWx0UmV0dXJuVmFsO1xuXG4gICAgICAgICAgICBvcHQuc2ltcGxlID0gdHJ1dGhpZnkob3B0aW9ucy5zaW1wbGUpO1xuICAgICAgICAgICAgaWYgKG9wdC5zaW1wbGUpe1xuICAgICAgICAgICAgICAgIHNldFNpbXBsZU9wdGlvbnMoKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHNldERlZmF1bHRPcHRpb25zKCk7XG4gICAgICAgICAgICAgICAgb3B0LnVzZUNhY2hlID0gdGVtcENhY2hlO1xuICAgICAgICAgICAgICAgIG9wdC5mb3JjZSA9IHRlbXBGb3JjZTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgIH1cbiAgICAgICAgaWYgKHR5cGVvZiBvcHRpb25zLmZvcmNlICE9PSAkVU5ERUZJTkVEKXtcbiAgICAgICAgICAgIG9wdC5mb3JjZSA9IHRydXRoaWZ5KG9wdGlvbnMuZm9yY2UpO1xuICAgICAgICB9XG4gICAgICAgIC8vIFRoZSBkZWZhdWx0IHJldHVybiB2YWx1ZSBtYXkgYmUgc2V0IHRvIHVuZGVmaW5lZCwgd2hpY2hcbiAgICAgICAgLy8gbWFrZXMgdGVzdGluZyBmb3IgdGhpcyBvcHRpb24gbW9yZSB0cmlja3kuXG4gICAgICAgIGlmIChPYmplY3Qua2V5cyhvcHRpb25zKS5pbmNsdWRlcygnZGVmYXVsdFJldHVyblZhbCcpKXtcbiAgICAgICAgICAgIG9wdFsnZGVmYXVsdFJldHVyblZhbCddID0gb3B0aW9ucy5kZWZhdWx0UmV0dXJuVmFsO1xuICAgICAgICB9XG4gICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIFNldHMgdXNlIG9mIGtleXBhdGggY2FjaGUgdG8gZW5hYmxlZCBvciBkaXNhYmxlZCwgZGVwZW5kaW5nIG9uIGlucHV0IHZhbHVlLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge0FueX0gdmFsIFZhbHVlIHdoaWNoIHdpbGwgYmUgaW50ZXJwcmV0ZWQgYXMgYSBib29sZWFuIHVzaW5nIGB0cnV0aGlmeWAuIFwidHJ1ZVwiIHdpbGwgZW5hYmxlIGNhY2hlOyBcImZhbHNlXCIgd2lsbCBkaXNhYmxlLlxuICAgICAqL1xuICAgIF90aGlzLnNldENhY2hlID0gZnVuY3Rpb24odmFsKXtcbiAgICAgICAgb3B0LnVzZUNhY2hlID0gdHJ1dGhpZnkodmFsKTtcbiAgICB9O1xuICAgIC8qKlxuICAgICAqIEVuYWJsZXMgdXNlIG9mIGtleXBhdGggY2FjaGUuXG4gICAgICogQHB1YmxpY1xuICAgICAqL1xuICAgIF90aGlzLnNldENhY2hlT24gPSBmdW5jdGlvbigpe1xuICAgICAgICBvcHQudXNlQ2FjaGUgPSB0cnVlO1xuICAgIH07XG4gICAgLyoqXG4gICAgICogRGlzYWJsZXMgdXNlIG9mIGtleXBhdGggY2FjaGUuXG4gICAgICogQHB1YmxpY1xuICAgICAqL1xuICAgIF90aGlzLnNldENhY2hlT2ZmID0gZnVuY3Rpb24oKXtcbiAgICAgICAgb3B0LnVzZUNhY2hlID0gZmFsc2U7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIFNldHMgXCJmb3JjZVwiIG9wdGlvbiB3aGVuIHNldHRpbmcgdmFsdWVzIGluIGFuIG9iamVjdCwgZGVwZW5kaW5nIG9uIGlucHV0IHZhbHVlLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge0FueX0gdmFsIFZhbHVlIHdoaWNoIHdpbGwgYmUgaW50ZXJwcmV0ZWQgYXMgYSBib29sZWFuIHVzaW5nIGB0cnV0aGlmeWAuIFwidHJ1ZVwiIGVuYWJsZXMgXCJmb3JjZVwiOyBcImZhbHNlXCIgZGlzYWJsZXMuXG4gICAgICovXG4gICAgX3RoaXMuc2V0Rm9yY2UgPSBmdW5jdGlvbih2YWwpe1xuICAgICAgICBvcHQuZm9yY2UgPSB0cnV0aGlmeSh2YWwpO1xuICAgIH07XG4gICAgLyoqXG4gICAgICogRW5hYmxlcyBcImZvcmNlXCIgb3B0aW9uIHdoZW4gc2V0dGluZyB2YWx1ZXMgaW4gYW4gb2JqZWN0LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKi9cbiAgICBfdGhpcy5zZXRGb3JjZU9uID0gZnVuY3Rpb24oKXtcbiAgICAgICAgb3B0LmZvcmNlID0gdHJ1ZTtcbiAgICB9O1xuICAgIC8qKlxuICAgICAqIERpc2FibGVzIFwiZm9yY2VcIiBvcHRpb24gd2hlbiBzZXR0aW5nIHZhbHVlcyBpbiBhbiBvYmplY3QuXG4gICAgICogQHB1YmxpY1xuICAgICAqL1xuICAgIF90aGlzLnNldEZvcmNlT2ZmID0gZnVuY3Rpb24oKXtcbiAgICAgICAgb3B0LmZvcmNlID0gZmFsc2U7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIFNob3J0Y3V0IGZ1bmN0aW9uIHRvIGFsdGVyIFBhdGhUb29sa2l0IHN5bnRheCB0byBhIFwic2ltcGxlXCIgbW9kZSB0aGF0IG9ubHkgdXNlc1xuICAgICAqIHNlcGFyYXRvcnMgYW5kIG5vIG90aGVyIG9wZXJhdG9ycy4gXCJTaW1wbGVcIiBtb2RlIGlzIGVuYWJsZWQgb3IgZGlzYWJsZWQgYWNjb3JkaW5nXG4gICAgICogdG8gdGhlIGZpcnN0IGFyZ3VtZW50IGFuZCB0aGUgc2VwYXJhdG9yIG1heSBiZSBjdXN0b21pemVkIHdpdGggdGhlIHNlY29uZFxuICAgICAqIGFyZ3VtZW50IHdoZW4gZW5hYmxpbmcgXCJzaW1wbGVcIiBtb2RlLlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge0FueX0gdmFsIFZhbHVlIHdoaWNoIHdpbGwgYmUgaW50ZXJwcmV0ZWQgYXMgYSBib29sZWFuIHVzaW5nIGB0cnV0aGlmeWAuIFwidHJ1ZVwiIGVuYWJsZXMgXCJzaW1wbGVcIiBtb2RlOyBcImZhbHNlXCIgZGlzYWJsZXMuXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHNlcCBTZXBhcmF0b3Igc3RyaW5nIHRvIHVzZSBpbiBwbGFjZSBvZiB0aGUgZGVmYXVsdCBcIi5cIlxuICAgICAqL1xuICAgIF90aGlzLnNldFNpbXBsZSA9IGZ1bmN0aW9uKHZhbCwgc2VwKXtcbiAgICAgICAgdmFyIHRlbXBDYWNoZSA9IG9wdC51c2VDYWNoZTsgLy8gcHJlc2VydmUgdGhlc2UgdHdvIG9wdGlvbnMgYWZ0ZXIgXCJzZXREZWZhdWx0T3B0aW9uc1wiXG4gICAgICAgIHZhciB0ZW1wRm9yY2UgPSBvcHQuZm9yY2U7XG4gICAgICAgIG9wdC5zaW1wbGUgPSB0cnV0aGlmeSh2YWwpO1xuICAgICAgICBpZiAob3B0LnNpbXBsZSl7XG4gICAgICAgICAgICBzZXRTaW1wbGVPcHRpb25zKHNlcCk7XG4gICAgICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgc2V0RGVmYXVsdE9wdGlvbnMoKTtcbiAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgICAgICBvcHQudXNlQ2FjaGUgPSB0ZW1wQ2FjaGU7XG4gICAgICAgICAgICBvcHQuZm9yY2UgPSB0ZW1wRm9yY2U7XG4gICAgICAgIH1cbiAgICAgICAgY2FjaGUgPSB7fTtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogRW5hYmxlcyBcInNpbXBsZVwiIG1vZGVcbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHNlcCBTZXBhcmF0b3Igc3RyaW5nIHRvIHVzZSBpbiBwbGFjZSBvZiB0aGUgZGVmYXVsdCBcIi5cIlxuICAgICAqIEBzZWUgc2V0U2ltcGxlXG4gICAgICovXG4gICAgX3RoaXMuc2V0U2ltcGxlT24gPSBmdW5jdGlvbihzZXApe1xuICAgICAgICBvcHQuc2ltcGxlID0gdHJ1ZTtcbiAgICAgICAgc2V0U2ltcGxlT3B0aW9ucyhzZXApO1xuICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICBjYWNoZSA9IHt9O1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBEaXNhYmxlcyBcInNpbXBsZVwiIG1vZGUsIHJlc3RvcmVzIGRlZmF1bHQgUGF0aFRvb2xraXQgc3ludGF4XG4gICAgICogQHB1YmxpY1xuICAgICAqIEBzZWUgc2V0U2ltcGxlXG4gICAgICogQHNlZSBzZXREZWZhdWx0T3B0aW9uc1xuICAgICAqL1xuICAgIF90aGlzLnNldFNpbXBsZU9mZiA9IGZ1bmN0aW9uKCl7XG4gICAgICAgIHZhciB0ZW1wQ2FjaGUgPSBvcHQudXNlQ2FjaGU7IC8vIHByZXNlcnZlIHRoZXNlIHR3byBvcHRpb25zIGFmdGVyIFwic2V0RGVmYXVsdE9wdGlvbnNcIlxuICAgICAgICB2YXIgdGVtcEZvcmNlID0gb3B0LmZvcmNlO1xuICAgICAgICBvcHQuc2ltcGxlID0gZmFsc2U7XG4gICAgICAgIHNldERlZmF1bHRPcHRpb25zKCk7XG4gICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgIG9wdC51c2VDYWNoZSA9IHRlbXBDYWNoZTtcbiAgICAgICAgb3B0LmZvcmNlID0gdGVtcEZvcmNlO1xuICAgICAgICBjYWNoZSA9IHt9O1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBTZXRzIGRlZmF1bHQgdmFsdWUgdG8gcmV0dXJuIGlmIFwiZ2V0XCIgcmVzb2x2ZXMgdG8gdW5kZWZpbmVkXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7QW55fSB2YWwgVmFsdWUgd2hpY2ggd2lsbCBiZSByZXR1cm5lZCB3aGVuIFwiZ2V0XCIgcmVzb2x2ZXMgdG8gdW5kZWZpbmVkXG4gICAgICovXG4gICAgX3RoaXMuc2V0RGVmYXVsdFJldHVyblZhbCA9IGZ1bmN0aW9uKHZhbCl7XG4gICAgICAgIG9wdFsnZGVmYXVsdFJldHVyblZhbCddID0gdmFsO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBNb2RpZnkgdGhlIHByb3BlcnR5IHNlcGFyYXRvciBpbiB0aGUgUGF0aFRvb2xraXQgc3ludGF4LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gdmFsIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGlzIG9wZXJhdGlvbi5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRTZXBhcmF0b3JQcm9wZXJ0eSA9IGZ1bmN0aW9uKHZhbCl7XG4gICAgICAgIGlmICh0eXBlb2YgdmFsID09PSAkU1RSSU5HICYmIHZhbC5sZW5ndGggPT09IDEpe1xuICAgICAgICAgICAgaWYgKHZhbCAhPT0gJFdJTERDQVJEICYmICghb3B0LnNlcGFyYXRvcnNbdmFsXSB8fCBvcHQuc2VwYXJhdG9yc1t2YWxdLmV4ZWMgPT09ICRQUk9QRVJUWSkgJiYgIShvcHQucHJlZml4ZXNbdmFsXSB8fCBvcHQuY29udGFpbmVyc1t2YWxdKSl7XG4gICAgICAgICAgICAgICAgdXBkYXRlT3B0aW9uQ2hhcihvcHQuc2VwYXJhdG9ycywgJFBST1BFUlRZLCB2YWwpO1xuICAgICAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0U2VwYXJhdG9yUHJvcGVydHkgLSB2YWx1ZSBhbHJlYWR5IGluIHVzZScpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRTZXBhcmF0b3JQcm9wZXJ0eSAtIGludmFsaWQgdmFsdWUnKTtcbiAgICAgICAgfVxuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBNb2RpZnkgdGhlIGNvbGxlY3Rpb24gc2VwYXJhdG9yIGluIHRoZSBQYXRoVG9vbGtpdCBzeW50YXguXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSB2YWwgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoaXMgb3BlcmF0aW9uLlxuICAgICAqL1xuICAgIF90aGlzLnNldFNlcGFyYXRvckNvbGxlY3Rpb24gPSBmdW5jdGlvbih2YWwpe1xuICAgICAgICBpZiAodHlwZW9mIHZhbCA9PT0gJFNUUklORyAmJiB2YWwubGVuZ3RoID09PSAxKXtcbiAgICAgICAgICAgIGlmICh2YWwgIT09ICRXSUxEQ0FSRCAmJiAoIW9wdC5zZXBhcmF0b3JzW3ZhbF0gfHwgb3B0LnNlcGFyYXRvcnNbdmFsXS5leGVjID09PSAkQ09MTEVDVElPTikgJiYgIShvcHQucHJlZml4ZXNbdmFsXSB8fCBvcHQuY29udGFpbmVyc1t2YWxdKSl7XG4gICAgICAgICAgICAgICAgdXBkYXRlT3B0aW9uQ2hhcihvcHQuc2VwYXJhdG9ycywgJENPTExFQ1RJT04sIHZhbCk7XG4gICAgICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRTZXBhcmF0b3JDb2xsZWN0aW9uIC0gdmFsdWUgYWxyZWFkeSBpbiB1c2UnKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0U2VwYXJhdG9yQ29sbGVjdGlvbiAtIGludmFsaWQgdmFsdWUnKTtcbiAgICAgICAgfVxuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBNb2RpZnkgdGhlIHBhcmVudCBwcmVmaXggaW4gdGhlIFBhdGhUb29sa2l0IHN5bnRheC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHZhbCBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhpcyBvcGVyYXRpb24uXG4gICAgICovXG4gICAgX3RoaXMuc2V0UHJlZml4UGFyZW50ID0gZnVuY3Rpb24odmFsKXtcbiAgICAgICAgaWYgKHR5cGVvZiB2YWwgPT09ICRTVFJJTkcgJiYgdmFsLmxlbmd0aCA9PT0gMSl7XG4gICAgICAgICAgICBpZiAodmFsICE9PSAkV0lMRENBUkQgJiYgKCFvcHQucHJlZml4ZXNbdmFsXSB8fCBvcHQucHJlZml4ZXNbdmFsXS5leGVjID09PSAkUEFSRU5UKSAmJiAhKG9wdC5zZXBhcmF0b3JzW3ZhbF0gfHwgb3B0LmNvbnRhaW5lcnNbdmFsXSkpe1xuICAgICAgICAgICAgICAgIHVwZGF0ZU9wdGlvbkNoYXIob3B0LnByZWZpeGVzLCAkUEFSRU5ULCB2YWwpO1xuICAgICAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0UHJlZml4UGFyZW50IC0gdmFsdWUgYWxyZWFkeSBpbiB1c2UnKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0UHJlZml4UGFyZW50IC0gaW52YWxpZCB2YWx1ZScpO1xuICAgICAgICB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIE1vZGlmeSB0aGUgcm9vdCBwcmVmaXggaW4gdGhlIFBhdGhUb29sa2l0IHN5bnRheC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHZhbCBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhpcyBvcGVyYXRpb24uXG4gICAgICovXG4gICAgX3RoaXMuc2V0UHJlZml4Um9vdCA9IGZ1bmN0aW9uKHZhbCl7XG4gICAgICAgIGlmICh0eXBlb2YgdmFsID09PSAkU1RSSU5HICYmIHZhbC5sZW5ndGggPT09IDEpe1xuICAgICAgICAgICAgaWYgKHZhbCAhPT0gJFdJTERDQVJEICYmICghb3B0LnByZWZpeGVzW3ZhbF0gfHwgb3B0LnByZWZpeGVzW3ZhbF0uZXhlYyA9PT0gJFJPT1QpICYmICEob3B0LnNlcGFyYXRvcnNbdmFsXSB8fCBvcHQuY29udGFpbmVyc1t2YWxdKSl7XG4gICAgICAgICAgICAgICAgdXBkYXRlT3B0aW9uQ2hhcihvcHQucHJlZml4ZXMsICRST09ULCB2YWwpO1xuICAgICAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0UHJlZml4Um9vdCAtIHZhbHVlIGFscmVhZHkgaW4gdXNlJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldFByZWZpeFJvb3QgLSBpbnZhbGlkIHZhbHVlJyk7XG4gICAgICAgIH1cbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogTW9kaWZ5IHRoZSBwbGFjZWhvbGRlciBwcmVmaXggaW4gdGhlIFBhdGhUb29sa2l0IHN5bnRheC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHZhbCBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhpcyBvcGVyYXRpb24uXG4gICAgICovXG4gICAgX3RoaXMuc2V0UHJlZml4UGxhY2Vob2xkZXIgPSBmdW5jdGlvbih2YWwpe1xuICAgICAgICBpZiAodHlwZW9mIHZhbCA9PT0gJFNUUklORyAmJiB2YWwubGVuZ3RoID09PSAxKXtcbiAgICAgICAgICAgIGlmICh2YWwgIT09ICRXSUxEQ0FSRCAmJiAoIW9wdC5wcmVmaXhlc1t2YWxdIHx8IG9wdC5wcmVmaXhlc1t2YWxdLmV4ZWMgPT09ICRQTEFDRUhPTERFUikgJiYgIShvcHQuc2VwYXJhdG9yc1t2YWxdIHx8IG9wdC5jb250YWluZXJzW3ZhbF0pKXtcbiAgICAgICAgICAgICAgICB1cGRhdGVPcHRpb25DaGFyKG9wdC5wcmVmaXhlcywgJFBMQUNFSE9MREVSLCB2YWwpO1xuICAgICAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0UHJlZml4UGxhY2Vob2xkZXIgLSB2YWx1ZSBhbHJlYWR5IGluIHVzZScpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRQcmVmaXhQbGFjZWhvbGRlciAtIGludmFsaWQgdmFsdWUnKTtcbiAgICAgICAgfVxuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBNb2RpZnkgdGhlIGNvbnRleHQgcHJlZml4IGluIHRoZSBQYXRoVG9vbGtpdCBzeW50YXguXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSB2YWwgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoaXMgb3BlcmF0aW9uLlxuICAgICAqL1xuICAgIF90aGlzLnNldFByZWZpeENvbnRleHQgPSBmdW5jdGlvbih2YWwpe1xuICAgICAgICBpZiAodHlwZW9mIHZhbCA9PT0gJFNUUklORyAmJiB2YWwubGVuZ3RoID09PSAxKXtcbiAgICAgICAgICAgIGlmICh2YWwgIT09ICRXSUxEQ0FSRCAmJiAoIW9wdC5wcmVmaXhlc1t2YWxdIHx8IG9wdC5wcmVmaXhlc1t2YWxdLmV4ZWMgPT09ICRDT05URVhUKSAmJiAhKG9wdC5zZXBhcmF0b3JzW3ZhbF0gfHwgb3B0LmNvbnRhaW5lcnNbdmFsXSkpe1xuICAgICAgICAgICAgICAgIHVwZGF0ZU9wdGlvbkNoYXIob3B0LnByZWZpeGVzLCAkQ09OVEVYVCwgdmFsKTtcbiAgICAgICAgICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldFByZWZpeENvbnRleHQgLSB2YWx1ZSBhbHJlYWR5IGluIHVzZScpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRQcmVmaXhDb250ZXh0IC0gaW52YWxpZCB2YWx1ZScpO1xuICAgICAgICB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIE1vZGlmeSB0aGUgcHJvcGVydHkgY29udGFpbmVyIGNoYXJhY3RlcnMgaW4gdGhlIFBhdGhUb29sa2l0IHN5bnRheC5cbiAgICAgKiBAcHVibGljXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IHZhbCBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhlIGNvbnRhaW5lciBvcGVuZXIuXG4gICAgICogQHBhcmFtIHtTdHJpbmd9IGNsb3NlciBOZXcgY2hhcmFjdGVyIHRvIHVzZSBmb3IgdGhlIGNvbnRhaW5lciBjbG9zZXIuXG4gICAgICovXG4gICAgX3RoaXMuc2V0Q29udGFpbmVyUHJvcGVydHkgPSBmdW5jdGlvbih2YWwsIGNsb3Nlcil7XG4gICAgICAgIGlmICh0eXBlb2YgdmFsID09PSAkU1RSSU5HICYmIHZhbC5sZW5ndGggPT09IDEgJiYgdHlwZW9mIGNsb3NlciA9PT0gJFNUUklORyAmJiBjbG9zZXIubGVuZ3RoID09PSAxKXtcbiAgICAgICAgICAgIGlmICh2YWwgIT09ICRXSUxEQ0FSRCAmJiAoIW9wdC5jb250YWluZXJzW3ZhbF0gfHwgb3B0LmNvbnRhaW5lcnNbdmFsXS5leGVjID09PSAkUFJPUEVSVFkpICYmICEob3B0LnNlcGFyYXRvcnNbdmFsXSB8fCBvcHQucHJlZml4ZXNbdmFsXSkpe1xuICAgICAgICAgICAgICAgIHVwZGF0ZU9wdGlvbkNoYXIob3B0LmNvbnRhaW5lcnMsICRQUk9QRVJUWSwgdmFsLCBjbG9zZXIpO1xuICAgICAgICAgICAgICAgIHVwZGF0ZVJlZ0V4KCk7XG4gICAgICAgICAgICAgICAgY2FjaGUgPSB7fTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0Q29udGFpbmVyUHJvcGVydHkgLSB2YWx1ZSBhbHJlYWR5IGluIHVzZScpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRDb250YWluZXJQcm9wZXJ0eSAtIGludmFsaWQgdmFsdWUnKTtcbiAgICAgICAgfVxuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBNb2RpZnkgdGhlIHNpbmdsZSBxdW90ZSBjb250YWluZXIgY2hhcmFjdGVycyBpbiB0aGUgUGF0aFRvb2xraXQgc3ludGF4LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gdmFsIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGUgY29udGFpbmVyIG9wZW5lci5cbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gY2xvc2VyIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGUgY29udGFpbmVyIGNsb3Nlci5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRDb250YWluZXJTaW5nbGVxdW90ZSA9IGZ1bmN0aW9uKHZhbCwgY2xvc2VyKXtcbiAgICAgICAgaWYgKHR5cGVvZiB2YWwgPT09ICRTVFJJTkcgJiYgdmFsLmxlbmd0aCA9PT0gMSAmJiB0eXBlb2YgY2xvc2VyID09PSAkU1RSSU5HICYmIGNsb3Nlci5sZW5ndGggPT09IDEpe1xuICAgICAgICAgICAgaWYgKHZhbCAhPT0gJFdJTERDQVJEICYmICghb3B0LmNvbnRhaW5lcnNbdmFsXSB8fCBvcHQuY29udGFpbmVyc1t2YWxdLmV4ZWMgPT09ICRTSU5HTEVRVU9URSkgJiYgIShvcHQuc2VwYXJhdG9yc1t2YWxdIHx8IG9wdC5wcmVmaXhlc1t2YWxdKSl7XG4gICAgICAgICAgICAgICAgdXBkYXRlT3B0aW9uQ2hhcihvcHQuY29udGFpbmVycywgJFNJTkdMRVFVT1RFLCB2YWwsIGNsb3Nlcik7XG4gICAgICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRDb250YWluZXJTaW5nbGVxdW90ZSAtIHZhbHVlIGFscmVhZHkgaW4gdXNlJyk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldENvbnRhaW5lclNpbmdsZXF1b3RlIC0gaW52YWxpZCB2YWx1ZScpO1xuICAgICAgICB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIE1vZGlmeSB0aGUgZG91YmxlIHF1b3RlIGNvbnRhaW5lciBjaGFyYWN0ZXJzIGluIHRoZSBQYXRoVG9vbGtpdCBzeW50YXguXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSB2YWwgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoZSBjb250YWluZXIgb3BlbmVyLlxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBjbG9zZXIgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoZSBjb250YWluZXIgY2xvc2VyLlxuICAgICAqL1xuICAgIF90aGlzLnNldENvbnRhaW5lckRvdWJsZXF1b3RlID0gZnVuY3Rpb24odmFsLCBjbG9zZXIpe1xuICAgICAgICBpZiAodHlwZW9mIHZhbCA9PT0gJFNUUklORyAmJiB2YWwubGVuZ3RoID09PSAxICYmIHR5cGVvZiBjbG9zZXIgPT09ICRTVFJJTkcgJiYgY2xvc2VyLmxlbmd0aCA9PT0gMSl7XG4gICAgICAgICAgICBpZiAodmFsICE9PSAkV0lMRENBUkQgJiYgKCFvcHQuY29udGFpbmVyc1t2YWxdIHx8IG9wdC5jb250YWluZXJzW3ZhbF0uZXhlYyA9PT0gJERPVUJMRVFVT1RFKSAmJiAhKG9wdC5zZXBhcmF0b3JzW3ZhbF0gfHwgb3B0LnByZWZpeGVzW3ZhbF0pKXtcbiAgICAgICAgICAgICAgICB1cGRhdGVPcHRpb25DaGFyKG9wdC5jb250YWluZXJzLCAkRE9VQkxFUVVPVEUsIHZhbCwgY2xvc2VyKTtcbiAgICAgICAgICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldENvbnRhaW5lckRvdWJsZXF1b3RlIC0gdmFsdWUgYWxyZWFkeSBpbiB1c2UnKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcignc2V0Q29udGFpbmVyRG91YmxlcXVvdGUgLSBpbnZhbGlkIHZhbHVlJyk7XG4gICAgICAgIH1cbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogTW9kaWZ5IHRoZSBmdW5jdGlvbiBjYWxsIGNvbnRhaW5lciBjaGFyYWN0ZXJzIGluIHRoZSBQYXRoVG9vbGtpdCBzeW50YXguXG4gICAgICogQHB1YmxpY1xuICAgICAqIEBwYXJhbSB7U3RyaW5nfSB2YWwgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoZSBjb250YWluZXIgb3BlbmVyLlxuICAgICAqIEBwYXJhbSB7U3RyaW5nfSBjbG9zZXIgTmV3IGNoYXJhY3RlciB0byB1c2UgZm9yIHRoZSBjb250YWluZXIgY2xvc2VyLlxuICAgICAqL1xuICAgIF90aGlzLnNldENvbnRhaW5lckNhbGwgPSBmdW5jdGlvbih2YWwsIGNsb3Nlcil7XG4gICAgICAgIGlmICh0eXBlb2YgdmFsID09PSAkU1RSSU5HICYmIHZhbC5sZW5ndGggPT09IDEgJiYgdHlwZW9mIGNsb3NlciA9PT0gJFNUUklORyAmJiBjbG9zZXIubGVuZ3RoID09PSAxKXtcbiAgICAgICAgICAgIGlmICh2YWwgIT09ICRXSUxEQ0FSRCAmJiAoIW9wdC5jb250YWluZXJzW3ZhbF0gfHwgb3B0LmNvbnRhaW5lcnNbdmFsXS5leGVjID09PSAkQ0FMTCkgJiYgIShvcHQuc2VwYXJhdG9yc1t2YWxdIHx8IG9wdC5wcmVmaXhlc1t2YWxdKSl7XG4gICAgICAgICAgICAgICAgdXBkYXRlT3B0aW9uQ2hhcihvcHQuY29udGFpbmVycywgJENBTEwsIHZhbCwgY2xvc2VyKTtcbiAgICAgICAgICAgICAgICB1cGRhdGVSZWdFeCgpO1xuICAgICAgICAgICAgICAgIGNhY2hlID0ge307XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ3NldENvbnRhaW5lckNhbGwgLSB2YWx1ZSBhbHJlYWR5IGluIHVzZScpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRDb250YWluZXJDYWxsIC0gaW52YWxpZCB2YWx1ZScpO1xuICAgICAgICB9XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIE1vZGlmeSB0aGUgZXZhbCBwcm9wZXJ0eSBjb250YWluZXIgY2hhcmFjdGVycyBpbiB0aGUgUGF0aFRvb2xraXQgc3ludGF4LlxuICAgICAqIEBwdWJsaWNcbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gdmFsIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGUgY29udGFpbmVyIG9wZW5lci5cbiAgICAgKiBAcGFyYW0ge1N0cmluZ30gY2xvc2VyIE5ldyBjaGFyYWN0ZXIgdG8gdXNlIGZvciB0aGUgY29udGFpbmVyIGNsb3Nlci5cbiAgICAgKi9cbiAgICBfdGhpcy5zZXRDb250YWluZXJFdmFsUHJvcGVydHkgPSBmdW5jdGlvbih2YWwsIGNsb3Nlcil7XG4gICAgICAgIGlmICh0eXBlb2YgdmFsID09PSAkU1RSSU5HICYmIHZhbC5sZW5ndGggPT09IDEgJiYgdHlwZW9mIGNsb3NlciA9PT0gJFNUUklORyAmJiBjbG9zZXIubGVuZ3RoID09PSAxKXtcbiAgICAgICAgICAgIGlmICh2YWwgIT09ICRXSUxEQ0FSRCAmJiAoIW9wdC5jb250YWluZXJzW3ZhbF0gfHwgb3B0LmNvbnRhaW5lcnNbdmFsXS5leGVjID09PSAkRVZBTFBST1BFUlRZKSAmJiAhKG9wdC5zZXBhcmF0b3JzW3ZhbF0gfHwgb3B0LnByZWZpeGVzW3ZhbF0pKXtcbiAgICAgICAgICAgICAgICB1cGRhdGVPcHRpb25DaGFyKG9wdC5jb250YWluZXJzLCAkRVZBTFBST1BFUlRZLCB2YWwsIGNsb3Nlcik7XG4gICAgICAgICAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgICAgICAgICBjYWNoZSA9IHt9O1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRDb250YWluZXJFdmFsUHJvcGVydHkgLSB2YWx1ZSBhbHJlYWR5IGluIHVzZScpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdzZXRDb250YWluZXJQcm9wZXJ0eSAtIGludmFsaWQgdmFsdWUnKTtcbiAgICAgICAgfVxuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBSZXNldCBhbGwgUGF0aFRvb2xraXQgb3B0aW9ucyB0byB0aGVpciBkZWZhdWx0IHZhbHVlcy5cbiAgICAgKiBAcHVibGljXG4gICAgICovXG4gICAgX3RoaXMucmVzZXRPcHRpb25zID0gZnVuY3Rpb24oKXtcbiAgICAgICAgc2V0RGVmYXVsdE9wdGlvbnMoKTtcbiAgICAgICAgdXBkYXRlUmVnRXgoKTtcbiAgICAgICAgY2FjaGUgPSB7fTtcbiAgICB9O1xuXG4gICAgLy8gSW5pdGlhbGl6ZSBvcHRpb24gc2V0XG4gICAgc2V0RGVmYXVsdE9wdGlvbnMoKTtcbiAgICB1cGRhdGVSZWdFeCgpO1xuXG4gICAgLy8gQXBwbHkgY3VzdG9tIG9wdGlvbnMgaWYgcHJvdmlkZWQgYXMgYXJndW1lbnQgdG8gY29uc3RydWN0b3JcbiAgICBvcHRpb25zICYmIF90aGlzLnNldE9wdGlvbnMob3B0aW9ucyk7XG5cbn07XG5cbmV4cG9ydCBkZWZhdWx0IFBhdGhUb29sa2l0O1xuIl0sIm5hbWVzIjpbXSwibWFwcGluZ3MiOiI7Ozs7OztBQUFBOzs7Ozs7O0FBT0EsQUFFQTtBQUNBLElBQUksS0FBSyxHQUFHLENBQUMsU0FBUyxDQUFDLENBQUMsQ0FBQyxPQUFPLENBQUMsQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDOzs7QUFHdkMsSUFBSSxTQUFTLE9BQU8sR0FBRztJQUNuQixVQUFVLE1BQU0sV0FBVztJQUMzQixPQUFPLFNBQVMsUUFBUTtJQUN4QixPQUFPLFNBQVMsUUFBUTtJQUN4QixLQUFLLFdBQVcsTUFBTTtJQUN0QixZQUFZLElBQUksYUFBYTtJQUM3QixRQUFRLFFBQVEsU0FBUztJQUN6QixTQUFTLE9BQU8sVUFBVTtJQUMxQixXQUFXLEtBQUssWUFBWTtJQUM1QixLQUFLLFdBQVcsTUFBTTtJQUN0QixZQUFZLElBQUksYUFBYTtJQUM3QixZQUFZLElBQUksYUFBYTtJQUM3QixLQUFLLFdBQVcsTUFBTTtJQUN0QixhQUFhLEdBQUcsY0FBYyxDQUFDOzs7Ozs7Ozs7Ozs7Ozs7Ozs7OztBQW9CbkMsSUFBSSxh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