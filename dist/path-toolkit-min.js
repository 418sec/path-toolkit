!function(e,t){"object"==typeof exports&&"undefined"!=typeof module?module.exports=t():"function"==typeof define&&define.amd?define(t):e.PathToolkit=t()}(this,function(){"use strict";var e=function(e){return e}(),t="*",r="undefined",o="string",i="parent",s="root",n="placeholder",p="context",a="property",c="collection",h="singlequote",f="doublequote",l="call",u="evalProperty",_=function(e){e._.prefixList=Object.keys(e._.opt.prefixes),e._.separatorList=Object.keys(e._.opt.separators),e._.containerList=Object.keys(e._.opt.containers),e._.containerCloseList=e._.containerList.map(function(t){return e._.opt.containers[t].closer}),e._.propertySeparator="",Object.keys(e._.opt.separators).forEach(function(t){e._.opt.separators[t].exec===a&&(e._.propertySeparator=t)}),e._.singlequote="",Object.keys(e._.opt.containers).forEach(function(t){e._.opt.containers[t].exec===h&&(e._.singlequote=t)}),e._.simplePathChars="[\\\\"+[t].concat(e._.prefixList).concat(e._.separatorList).concat(e._.containerList).join("\\").replace("\\"+e._.propertySeparator,"")+"]",e._.simplePathRegEx=new RegExp(e._.simplePathChars),e._.allSpecials="[\\\\\\"+[t].concat(e._.prefixList).concat(e._.separatorList).concat(e._.containerList).concat(e._.containerCloseList).join("\\")+"]",e._.allSpecialsRegEx=new RegExp(e._.allSpecials,"g"),e._.escapedNonSpecialsRegEx=new RegExp("\\"+e._.allSpecials.replace(/^\[/,"[^")),e._.wildcardRegEx=new RegExp("\\"+t)},y=function(e){e._.opt=e._.opt||{},e._.opt.useCache=!0,e._.opt.simple=!1,e._.opt.force=!1,e._.opt.prefixes={"<":{exec:i},"~":{exec:s},"%":{exec:n},"@":{exec:p}},e._.opt.separators={".":{exec:a},",":{exec:c}},e._.opt.containers={"[":{closer:"]",exec:a},"'":{closer:"'",exec:h},'"':{closer:'"',exec:f},"(":{closer:")",exec:l},"{":{closer:"}",exec:u}}},x=function(e,r){var o=(e.indexOf(t),e.split(t,2)),i=!0;if(o[0]){if(o[0]===e)return o[0]===r;i=i&&r.substr(0,o[0].length)===o[0]}return o[1]&&(i=i&&r.substr(-1*o[1].length)===o[1]),i},w=function(e){return typeof e===r||null===e?!1:"function"==typeof e||"object"==typeof e},d=function(e){var t;return typeof e!==o?e&&!0:(t=e.toUpperCase(),"TRUE"===t||"YES"===t||"ON"===t)},g=function(r,i){var s="",n=[],p=[],l={},u=0,_="",y=!1,x="",w=0,d="",v="",C="",E=[],P=0,m=0;if(r._.opt.useCache&&r._.cache[i]!==e)return r._.cache[i];if(s=i.replace(r._.escapedNonSpecialsRegEx,"$&".substr(1)),u=s.length,typeof i===o&&!r._.simplePathRegEx.test(i))return n=s.split(r._.propertySeparator),r._.opt.useCache&&(r._.cache[i]=n),n;for(w=0;u>w;w++){if(m||"\\"!==s[w]||(m=w+1,w++),s[w]===t&&(y=!0),P>0)if(!m&&s[w]===d&&d!==v.closer&&P++,!m&&s[w]===v.closer&&P--,P>0)x+=s[w];else{if(u>w+1&&r._.opt.separators[s[w+1]]&&r._.opt.separators[s[w+1]].exec===c){if(p=g(r,x),p===e)return;E.push({t:p,exec:v.exec})}else if(E[0]){if(p=g(r,x),p===e)return;E.push({t:p,exec:v.exec}),n.push(E),E=[]}else if(v.exec===a){if(p=g(r,x),p===e)return;n=n.concat(p)}else if(v.exec===h||v.exec===f)n.push(x);else{if(p=g(r,x),p===e)return;n.push({t:p,exec:v.exec})}x=""}else if(!m&&s[w]in r._.opt.prefixes&&r._.opt.prefixes[s[w]].exec)l.has=!0,l[r._.opt.prefixes[s[w]].exec]?l[r._.opt.prefixes[s[w]].exec]++:l[r._.opt.prefixes[s[w]].exec]=1;else if(!m&&r._.opt.separators.hasOwnProperty(s[w])&&r._.opt.separators[s[w]].exec){if(C=r._.opt.separators[s[w]],!_&&(l.has||y))return;_&&(l.has||y)&&(_={w:_,mods:l},l={}),C.exec===a?E[0]!==e?(_&&E.push(_),n.push(E),E=[]):_&&n.push(_):C.exec===c&&_&&E.push(_),_="",y=!1}else!m&&r._.opt.containers.hasOwnProperty(s[w])&&r._.opt.containers[s[w]].exec?(v=r._.opt.containers[s[w]],_&&(l.has||y)&&(_={w:_,mods:l},l={}),E[0]!==e?_&&E.push(_):_&&n.push(_),_="",y=!1,d=s[w],P++):u>w&&(_+=s[w]);u>w&&w===m&&(m=0)}return m||(_&&(l.has||y)&&(_={w:_,mods:l},l={}),E[0]!==e?(_&&E.push(_),n.push(E)):_&&n.push(_),0!==P)?void 0:(r._.opt.useCache&&(r._.cache[i]=n),n)},v=function(t,r,i,s,n,p){var a,c,h,f=s!==e,_=[],y=0,w=0,d=1,C=0,E=r,P="",m=0,O="",S=0,R=r,b=!1,A=0,j="";if(typeof i===o){if(t._.opt.useCache&&t._.cache[i])_=t._.cache[i];else if(_=g(t,i),_===e)return}else _=i.t?i.t:[i];if(y=_.length,0!==y){for(w=y-1,p?d=p.length:p=[r];E!==e&&y>S;){if(P=_[S],b=f&&S===w,typeof P===o){if(f)if(b){if(R[P]=s,R[P]!==s)return}else t._.opt.force&&(Array.isArray(E)?R[P]!==e:!R.hasOwnProperty(P))&&(R[P]={});c=R[P]}else if(P===e)c=void 0;else if(Array.isArray(P))for(c=[],m=P.length,C=0;m>C;C++){if(a=v(t,R,P[C],s,n,p.slice()),a===e)return;b?P[C].t&&P[C].exec===u?R[a]=s:c=c.concat(a):c=P[C].t&&P[C].exec===u?c.concat(R[a]):c.concat(a)}else if(P.w){if(O=P.w+"",P.mods.parent&&(R=p[d-1-P.mods.parent],R===e))return;if(P.mods.root&&(R=p[0],p=[R],d=1),P.mods.placeholder){if(A=O-1,n[A]===e)return;O=n[A].toString()}if(P.mods.context){if(A=O-1,n[A]===e)return;c=n[A]}else if(R[O]!==e)b&&(R[O]=s),c=R[O];else if("function"==typeof R)c=O;else{if(!(t._.wildcardRegEx.test(O)>-1))return;c=[];for(j in R)R.hasOwnProperty(j)&&x(O,j)&&(b&&(R[j]=s),c.push(R[j]))}}else P.exec===u?(b&&(R[v(t,R,P,e,n,p.slice())]=s),c=R[v(t,R,P,e,n,p.slice())]):P.exec===l&&(P.t&&P.t.length?(h=v(t,R,P,e,n),c=h===e?R.apply(p[d-2]):Array.isArray(h)?R.apply(p[d-2],h):R.call(p[d-2],h)):c=R.call(p[d-2]));p.push(c),d++,R=c,E=c,S++}return R}},C=function(t,r,o,i){var s=i!==e,n=[],p=0,a=0;for(n=o.split(t._.propertySeparator),a=n.length;r!==e&&a>p;){if(""===n[p])return;s&&(p===a-1?r[n[p]]=i:t._.opt.force&&(Array.isArray(r)?r[n[p]]!==e:!r.hasOwnProperty(n[p]))&&(r[n[p]]={})),r=r[n[p++]]}return r},E=function(t,r,o,i){for(var s=i!==e,n=0,p=o.length;null!=r&&p>n;){if(""===o[n])return;s&&(n===p-1?r[o[n]]=i:t._.opt.force&&(Array.isArray(r)?r[o[n]]!==e:!r.hasOwnProperty(o[n]))&&(r[o[n]]={})),r=r[o[n++]]}return r},P=function(e,t){var r=new RegExp(e,"g");return e+t.replace(r,"\\"+e)+e},m=function(e,t,r,o,i){var s,n,p,a,c;if(i=i?i:"",t===r)return o(i);if(Array.isArray(t)){for(n=t.length,s=0;n>s;s++)if(p=m(e,t[s],r,o,i+e._.propertySeparator+s),!p)return;return!0}if(w(t)){for(a=Object.keys(t),n=a.length,n>1&&(a=a.sort()),s=0;n>s;s++)if(t.hasOwnProperty(a[s])&&(c=a[s],e._.allSpecialsRegEx.test(c)&&(c=P(e._.singlequote,c)),p=m(e,t[a[s]],r,o,i+e._.propertySeparator+c),!p))return;return!0}return!0},O=function(e){this._={},this._.cache={},y(this),_(this),e&&this.setOptions(e)};O.prototype.getTokens=function(e){var t=g(this,e);if(typeof t!==r)return{t:t}},O.prototype.isValid=function(e){return typeof g(this,e)!==r},O.prototype.escape=function(e){return e.replace(this._.allSpecialsRegEx,"\\$&")},O.prototype.get=function(e,t){var r,i=0,s=arguments.length;if(typeof t===o&&!this._.simplePathRegEx.test(t))return C(this,e,t);if(Object.hasOwnProperty.call(t,"t")&&Array.isArray(t.t)){for(i=t.t.length-1;i>=0;i--)if(typeof t.t[i]!==o){if(r=[],s>2)for(i=2;s>i;i++)r[i-2]=arguments[i];return v(this,e,t,void 0,r)}return E(this,e,t.t)}if(r=[],s>2)for(i=2;s>i;i++)r[i-2]=arguments[i];return v(this,e,t,void 0,r)},O.prototype.set=function(t,r,i){var s,n,p=0,a=arguments.length,c=!1;if(typeof r!==o||this._.simplePathRegEx.test(r))if(Object.hasOwnProperty.call(r,"t")&&Array.isArray(r.t)){for(p=r.t.length-1;p>=0;p--)if(!c&&typeof r.t[p]!==o){if(s=[],a>3)for(p=3;a>p;p++)s[p-3]=arguments[p];n=v(this,t,r,i,s),c=!0}c||(n=E(this,t,r.t,i))}else{if(a>3)for(s=[],p=3;a>p;p++)s[p-3]=arguments[p];n=v(this,t,r,i,s)}else n=C(this,t,r,i),c=!0;return Array.isArray(n)?-1===n.indexOf(void 0):n!==e},O.prototype.find=function(e,t,r){var o=[],i=function(e){return o.push(e.substr(1)),r&&"one"!==r?!0:(o=o[0],!1)};return m(this,e,t,i),o[0]?o:void 0};var S=function(e,t,r,o,i){var s="";Object.keys(t).forEach(function(e){t[e].exec===r&&(s=e)}),delete t[s],t[o]={exec:r},i&&(t[o].closer=i)},R=function(e,t){var r={};typeof t===o&&1===t.length||(t="."),r[t]={exec:a},e._.opt.prefixes={},e._.opt.containers={},e._.opt.separators=r};return O.prototype.setOptions=function(e){if(e.prefixes&&(this._.opt.prefixes=e.prefixes,this._.cache={}),e.separators&&(this._.opt.separators=e.separators,this._.cache={}),e.containers&&(this._.opt.containers=e.containers,this._.cache={}),typeof e.cache!==r&&(this._.opt.useCache=!!e.cache),typeof e.simple!==r){var t=this._.opt.useCache,o=this._.opt.force;this._.opt.simple=d(e.simple),this._.opt.simple?R(this):(y(this),this._.opt.useCache=t,this._.opt.force=o),this._.cache={}}typeof e.force!==r&&(this._.opt.force=d(e.force)),_(this)},O.prototype.setCache=function(e){this._.opt.useCache=d(e)},O.prototype.setCacheOn=function(){this._.opt.useCache=!0},O.prototype.setCacheOff=function(){this._.opt.useCache=!1},O.prototype.setForce=function(e){this._.opt.force=d(e)},O.prototype.setForceOn=function(){this._.opt.force=!0},O.prototype.setForceOff=function(){this._.opt.force=!1},O.prototype.setSimple=function(e,t){var r=this._.opt.useCache,o=this._.opt.force;this._.opt.simple=d(e),this._.opt.simple?(R(this,t),_(this)):(y(this),_(this),this._.opt.useCache=r,this._.opt.force=o),this._.cache={}},O.prototype.setSimpleOn=function(e){this._.opt.simple=!0,R(this,e),_(this),this._.cache={}},O.prototype.setSimpleOff=function(){var e=this._.opt.useCache,t=this._.opt.force;this._.opt.simple=!1,y(this),_(this),this._.opt.useCache=e,this._.opt.force=t,this._.cache={}},O.prototype.setSeparatorProperty=function(e){if(typeof e!==o||1!==e.length)throw new Error("setSeparatorProperty - invalid value");if(e===t||this._.opt.separators[e]&&this._.opt.separators[e].exec!==a||this._.opt.prefixes[e]||this._.opt.containers[e])throw new Error("setSeparatorProperty - value already in use");S(this,this._.opt.separators,a,e),_(this),this._.cache={}},O.prototype.setSeparatorCollection=function(e){if(typeof e!==o||1!==e.length)throw new Error("setSeparatorCollection - invalid value");if(e===t||this._.opt.separators[e]&&this._.opt.separators[e].exec!==c||this._.opt.prefixes[e]||this._.opt.containers[e])throw new Error("setSeparatorCollection - value already in use");S(this,this._.opt.separators,c,e),_(this),this._.cache={}},O.prototype.setPrefixParent=function(e){if(typeof e!==o||1!==e.length)throw new Error("setPrefixParent - invalid value");if(e===t||this._.opt.prefixes[e]&&this._.opt.prefixes[e].exec!==i||this._.opt.separators[e]||this._.opt.containers[e])throw new Error("setPrefixParent - value already in use");S(this,this._.opt.prefixes,i,e),_(this),this._.cache={}},O.prototype.setPrefixRoot=function(e){if(typeof e!==o||1!==e.length)throw new Error("setPrefixRoot - invalid value");if(e===t||this._.opt.prefixes[e]&&this._.opt.prefixes[e].exec!==s||this._.opt.separators[e]||this._.opt.containers[e])throw new Error("setPrefixRoot - value already in use");S(this,this._.opt.prefixes,s,e),_(this),this._.cache={}},O.prototype.setPrefixPlaceholder=function(e){if(typeof e!==o||1!==e.length)throw new Error("setPrefixPlaceholder - invalid value");if(e===t||this._.opt.prefixes[e]&&this._.opt.prefixes[e].exec!==n||this._.opt.separators[e]||this._.opt.containers[e])throw new Error("setPrefixPlaceholder - value already in use");S(this,this._.opt.prefixes,n,e),_(this),this._.cache={}},O.prototype.setPrefixContext=function(e){if(typeof e!==o||1!==e.length)throw new Error("setPrefixContext - invalid value");if(e===t||this._.opt.prefixes[e]&&this._.opt.prefixes[e].exec!==p||this._.opt.separators[e]||this._.opt.containers[e])throw new Error("setPrefixContext - value already in use");S(this,this._.opt.prefixes,p,e),_(this),this._.cache={}},O.prototype.setContainerProperty=function(e,r){if(typeof e!==o||1!==e.length||typeof r!==o||1!==r.length)throw new Error("setContainerProperty - invalid value");if(e===t||this._.opt.containers[e]&&this._.opt.containers[e].exec!==a||this._.opt.separators[e]||this._.opt.prefixes[e])throw new Error("setContainerProperty - value already in use");S(this,this._.opt.containers,a,e,r),_(this),this._.cache={}},O.prototype.setContainerSinglequote=function(e,r){if(typeof e!==o||1!==e.length||typeof r!==o||1!==r.length)throw new Error("setContainerSinglequote - invalid value");if(e===t||this._.opt.containers[e]&&this._.opt.containers[e].exec!==h||this._.opt.separators[e]||this._.opt.prefixes[e])throw new Error("setContainerSinglequote - value already in use");S(this,this._.opt.containers,h,e,r),_(this),this._.cache={}},O.prototype.setContainerDoublequote=function(e,r){if(typeof e!==o||1!==e.length||typeof r!==o||1!==r.length)throw new Error("setContainerDoublequote - invalid value");if(e===t||this._.opt.containers[e]&&this._.opt.containers[e].exec!==f||this._.opt.separators[e]||this._.opt.prefixes[e])throw new Error("setContainerDoublequote - value already in use");S(this,this._.opt.containers,f,e,r),_(this),this._.cache={}},O.prototype.setContainerCall=function(e,r){if(typeof e!==o||1!==e.length||typeof r!==o||1!==r.length)throw new Error("setContainerCall - invalid value");if(e===t||this._.opt.containers[e]&&this._.opt.containers[e].exec!==l||this._.opt.separators[e]||this._.opt.prefixes[e])throw new Error("setContainerCall - value already in use");S(this,this._.opt.containers,l,e,r),_(this),this._.cache={}},O.prototype.setContainerEvalProperty=function(e,r){if(typeof e!==o||1!==e.length||typeof r!==o||1!==r.length)throw new Error("setContainerProperty - invalid value");if(e===t||this._.opt.containers[e]&&this._.opt.containers[e].exec!==u||this._.opt.separators[e]||this._.opt.prefixes[e])throw new Error("setContainerEvalProperty - value already in use");S(this,this._.opt.containers,u,e,r),_(this),this._.cache={}},O.prototype.resetOptions=function(){y(this),_(this),this._.cache={}},O});
//# sourceMappingURL=path-toolkit-min.js.map