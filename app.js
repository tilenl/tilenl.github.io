import {randomBytes, createHash} from "crypto";
import http from "http";
import https from "https";
import zlib from "zlib";
import Stream, {PassThrough, pipeline} from "stream";
import {types} from "util";
import {format, parse, resolve} from "url";
var chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_$";
var unsafeChars = /[<>\b\f\n\r\t\0\u2028\u2029]/g;
var reserved = /^(?:do|if|in|for|int|let|new|try|var|byte|case|char|else|enum|goto|long|this|void|with|await|break|catch|class|const|final|float|short|super|throw|while|yield|delete|double|export|import|native|return|switch|throws|typeof|boolean|default|extends|finally|package|private|abstract|continue|debugger|function|volatile|interface|protected|transient|implements|instanceof|synchronized)$/;
var escaped$1 = {
  "<": "\\u003C",
  ">": "\\u003E",
  "/": "\\u002F",
  "\\": "\\\\",
  "\b": "\\b",
  "\f": "\\f",
  "\n": "\\n",
  "\r": "\\r",
  "	": "\\t",
  "\0": "\\0",
  "\u2028": "\\u2028",
  "\u2029": "\\u2029"
};
var objectProtoOwnPropertyNames = Object.getOwnPropertyNames(Object.prototype).sort().join("\0");
function devalue(value) {
  var counts = new Map();
  function walk(thing) {
    if (typeof thing === "function") {
      throw new Error("Cannot stringify a function");
    }
    if (counts.has(thing)) {
      counts.set(thing, counts.get(thing) + 1);
      return;
    }
    counts.set(thing, 1);
    if (!isPrimitive(thing)) {
      var type = getType(thing);
      switch (type) {
        case "Number":
        case "String":
        case "Boolean":
        case "Date":
        case "RegExp":
          return;
        case "Array":
          thing.forEach(walk);
          break;
        case "Set":
        case "Map":
          Array.from(thing).forEach(walk);
          break;
        default:
          var proto = Object.getPrototypeOf(thing);
          if (proto !== Object.prototype && proto !== null && Object.getOwnPropertyNames(proto).sort().join("\0") !== objectProtoOwnPropertyNames) {
            throw new Error("Cannot stringify arbitrary non-POJOs");
          }
          if (Object.getOwnPropertySymbols(thing).length > 0) {
            throw new Error("Cannot stringify POJOs with symbolic keys");
          }
          Object.keys(thing).forEach(function(key) {
            return walk(thing[key]);
          });
      }
    }
  }
  walk(value);
  var names = new Map();
  Array.from(counts).filter(function(entry) {
    return entry[1] > 1;
  }).sort(function(a, b) {
    return b[1] - a[1];
  }).forEach(function(entry, i) {
    names.set(entry[0], getName(i));
  });
  function stringify(thing) {
    if (names.has(thing)) {
      return names.get(thing);
    }
    if (isPrimitive(thing)) {
      return stringifyPrimitive(thing);
    }
    var type = getType(thing);
    switch (type) {
      case "Number":
      case "String":
      case "Boolean":
        return "Object(" + stringify(thing.valueOf()) + ")";
      case "RegExp":
        return "new RegExp(" + stringifyString(thing.source) + ', "' + thing.flags + '")';
      case "Date":
        return "new Date(" + thing.getTime() + ")";
      case "Array":
        var members = thing.map(function(v, i) {
          return i in thing ? stringify(v) : "";
        });
        var tail = thing.length === 0 || thing.length - 1 in thing ? "" : ",";
        return "[" + members.join(",") + tail + "]";
      case "Set":
      case "Map":
        return "new " + type + "([" + Array.from(thing).map(stringify).join(",") + "])";
      default:
        var obj = "{" + Object.keys(thing).map(function(key) {
          return safeKey(key) + ":" + stringify(thing[key]);
        }).join(",") + "}";
        var proto = Object.getPrototypeOf(thing);
        if (proto === null) {
          return Object.keys(thing).length > 0 ? "Object.assign(Object.create(null)," + obj + ")" : "Object.create(null)";
        }
        return obj;
    }
  }
  var str = stringify(value);
  if (names.size) {
    var params_1 = [];
    var statements_1 = [];
    var values_1 = [];
    names.forEach(function(name, thing) {
      params_1.push(name);
      if (isPrimitive(thing)) {
        values_1.push(stringifyPrimitive(thing));
        return;
      }
      var type = getType(thing);
      switch (type) {
        case "Number":
        case "String":
        case "Boolean":
          values_1.push("Object(" + stringify(thing.valueOf()) + ")");
          break;
        case "RegExp":
          values_1.push(thing.toString());
          break;
        case "Date":
          values_1.push("new Date(" + thing.getTime() + ")");
          break;
        case "Array":
          values_1.push("Array(" + thing.length + ")");
          thing.forEach(function(v, i) {
            statements_1.push(name + "[" + i + "]=" + stringify(v));
          });
          break;
        case "Set":
          values_1.push("new Set");
          statements_1.push(name + "." + Array.from(thing).map(function(v) {
            return "add(" + stringify(v) + ")";
          }).join("."));
          break;
        case "Map":
          values_1.push("new Map");
          statements_1.push(name + "." + Array.from(thing).map(function(_a) {
            var k = _a[0], v = _a[1];
            return "set(" + stringify(k) + ", " + stringify(v) + ")";
          }).join("."));
          break;
        default:
          values_1.push(Object.getPrototypeOf(thing) === null ? "Object.create(null)" : "{}");
          Object.keys(thing).forEach(function(key) {
            statements_1.push("" + name + safeProp(key) + "=" + stringify(thing[key]));
          });
      }
    });
    statements_1.push("return " + str);
    return "(function(" + params_1.join(",") + "){" + statements_1.join(";") + "}(" + values_1.join(",") + "))";
  } else {
    return str;
  }
}
function getName(num) {
  var name = "";
  do {
    name = chars[num % chars.length] + name;
    num = ~~(num / chars.length) - 1;
  } while (num >= 0);
  return reserved.test(name) ? name + "_" : name;
}
function isPrimitive(thing) {
  return Object(thing) !== thing;
}
function stringifyPrimitive(thing) {
  if (typeof thing === "string")
    return stringifyString(thing);
  if (thing === void 0)
    return "void 0";
  if (thing === 0 && 1 / thing < 0)
    return "-0";
  var str = String(thing);
  if (typeof thing === "number")
    return str.replace(/^(-)?0\./, "$1.");
  return str;
}
function getType(thing) {
  return Object.prototype.toString.call(thing).slice(8, -1);
}
function escapeUnsafeChar(c) {
  return escaped$1[c] || c;
}
function escapeUnsafeChars(str) {
  return str.replace(unsafeChars, escapeUnsafeChar);
}
function safeKey(key) {
  return /^[_$a-zA-Z][_$a-zA-Z0-9]*$/.test(key) ? key : escapeUnsafeChars(JSON.stringify(key));
}
function safeProp(key) {
  return /^[_$a-zA-Z][_$a-zA-Z0-9]*$/.test(key) ? "." + key : "[" + escapeUnsafeChars(JSON.stringify(key)) + "]";
}
function stringifyString(str) {
  var result = '"';
  for (var i = 0; i < str.length; i += 1) {
    var char = str.charAt(i);
    var code = char.charCodeAt(0);
    if (char === '"') {
      result += '\\"';
    } else if (char in escaped$1) {
      result += escaped$1[char];
    } else if (code >= 55296 && code <= 57343) {
      var next = str.charCodeAt(i + 1);
      if (code <= 56319 && (next >= 56320 && next <= 57343)) {
        result += char + str[++i];
      } else {
        result += "\\u" + code.toString(16).toUpperCase();
      }
    } else {
      result += char;
    }
  }
  result += '"';
  return result;
}
function noop() {
}
function safe_not_equal(a, b) {
  return a != a ? b == b : a !== b || (a && typeof a === "object" || typeof a === "function");
}
const subscriber_queue = [];
function writable(value, start = noop) {
  let stop;
  const subscribers = [];
  function set(new_value) {
    if (safe_not_equal(value, new_value)) {
      value = new_value;
      if (stop) {
        const run_queue = !subscriber_queue.length;
        for (let i = 0; i < subscribers.length; i += 1) {
          const s2 = subscribers[i];
          s2[1]();
          subscriber_queue.push(s2, value);
        }
        if (run_queue) {
          for (let i = 0; i < subscriber_queue.length; i += 2) {
            subscriber_queue[i][0](subscriber_queue[i + 1]);
          }
          subscriber_queue.length = 0;
        }
      }
    }
  }
  function update(fn) {
    set(fn(value));
  }
  function subscribe(run2, invalidate = noop) {
    const subscriber = [run2, invalidate];
    subscribers.push(subscriber);
    if (subscribers.length === 1) {
      stop = start(set) || noop;
    }
    run2(value);
    return () => {
      const index2 = subscribers.indexOf(subscriber);
      if (index2 !== -1) {
        subscribers.splice(index2, 1);
      }
      if (subscribers.length === 0) {
        stop();
        stop = null;
      }
    };
  }
  return {set, update, subscribe};
}
const s$1 = JSON.stringify;
async function render_response({
  options,
  $session,
  page_config,
  status,
  error: error2,
  branch,
  page
}) {
  const css2 = new Set();
  const js = new Set();
  const styles = new Set();
  const serialized_data = [];
  let rendered;
  let is_private = false;
  let maxage;
  if (branch) {
    branch.forEach(({node, loaded, fetched, uses_credentials}) => {
      if (node.css)
        node.css.forEach((url) => css2.add(url));
      if (node.js)
        node.js.forEach((url) => js.add(url));
      if (node.styles)
        node.styles.forEach((content) => styles.add(content));
      if (fetched && page_config.hydrate)
        serialized_data.push(...fetched);
      if (uses_credentials)
        is_private = true;
      maxage = loaded.maxage;
    });
    if (error2) {
      if (options.dev) {
        error2.stack = await options.get_stack(error2);
      } else {
        error2.stack = String(error2);
      }
    }
    const session = writable($session);
    const props = {
      stores: {
        page: writable(null),
        navigating: writable(null),
        session
      },
      page,
      components: branch.map(({node}) => node.module.default)
    };
    for (let i = 0; i < branch.length; i += 1) {
      props[`props_${i}`] = await branch[i].loaded.props;
    }
    let session_tracking_active = false;
    const unsubscribe = session.subscribe(() => {
      if (session_tracking_active)
        is_private = true;
    });
    session_tracking_active = true;
    try {
      rendered = options.root.render(props);
    } finally {
      unsubscribe();
    }
  } else {
    rendered = {head: "", html: "", css: ""};
  }
  const links = options.amp ? styles.size > 0 ? `<style amp-custom>${Array.from(styles).join("\n")}</style>` : "" : [
    ...Array.from(js).map((dep) => `<link rel="modulepreload" href="${dep}">`),
    ...Array.from(css2).map((dep) => `<link rel="stylesheet" href="${dep}">`)
  ].join("\n		");
  let init2 = "";
  if (options.amp) {
    init2 = `
		<style amp-boilerplate>body{-webkit-animation:-amp-start 8s steps(1,end) 0s 1 normal both;-moz-animation:-amp-start 8s steps(1,end) 0s 1 normal both;-ms-animation:-amp-start 8s steps(1,end) 0s 1 normal both;animation:-amp-start 8s steps(1,end) 0s 1 normal both}@-webkit-keyframes -amp-start{from{visibility:hidden}to{visibility:visible}}@-moz-keyframes -amp-start{from{visibility:hidden}to{visibility:visible}}@-ms-keyframes -amp-start{from{visibility:hidden}to{visibility:visible}}@-o-keyframes -amp-start{from{visibility:hidden}to{visibility:visible}}@keyframes -amp-start{from{visibility:hidden}to{visibility:visible}}</style>
		<noscript><style amp-boilerplate>body{-webkit-animation:none;-moz-animation:none;-ms-animation:none;animation:none}</style></noscript>
		<script async src="https://cdn.ampproject.org/v0.js"></script>`;
  } else if (page_config.router || page_config.hydrate) {
    init2 = `<script type="module">
			import { start } from ${s$1(options.entry)};
			start({
				target: ${options.target ? `document.querySelector(${s$1(options.target)})` : "document.body"},
				paths: ${s$1(options.paths)},
				session: ${try_serialize($session, (error3) => {
      throw new Error(`Failed to serialize session data: ${error3.message}`);
    })},
				host: ${page.host ? s$1(page.host) : "location.host"},
				route: ${!!page_config.router},
				spa: ${!page_config.ssr},
				hydrate: ${page_config.ssr && page_config.hydrate ? `{
					status: ${status},
					error: ${serialize_error(error2)},
					nodes: [
						${branch.map(({node}) => `import(${s$1(node.entry)})`).join(",\n						")}
					],
					page: {
						host: ${page.host ? s$1(page.host) : "location.host"}, // TODO this is redundant
						path: ${s$1(page.path)},
						query: new URLSearchParams(${s$1(page.query.toString())}),
						params: ${s$1(page.params)}
					}
				}` : "null"}
			});
		</script>`;
  }
  const head = [
    rendered.head,
    styles.size && !options.amp ? `<style data-svelte>${Array.from(styles).join("\n")}</style>` : "",
    links,
    init2
  ].join("\n\n		");
  const body = options.amp ? rendered.html : `${rendered.html}

			${serialized_data.map(({url, json}) => `<script type="svelte-data" url="${url}">${json}</script>`).join("\n\n			")}
		`.replace(/^\t{2}/gm, "");
  const headers = {
    "content-type": "text/html"
  };
  if (maxage) {
    headers["cache-control"] = `${is_private ? "private" : "public"}, max-age=${maxage}`;
  }
  return {
    status,
    headers,
    body: options.template({head, body})
  };
}
function try_serialize(data, fail) {
  try {
    return devalue(data);
  } catch (err) {
    if (fail)
      fail(err);
    return null;
  }
}
function serialize_error(error2) {
  if (!error2)
    return null;
  let serialized = try_serialize(error2);
  if (!serialized) {
    const {name, message, stack} = error2;
    serialized = try_serialize({name, message, stack});
  }
  if (!serialized) {
    serialized = "{}";
  }
  return serialized;
}
function dataUriToBuffer(uri) {
  if (!/^data:/i.test(uri)) {
    throw new TypeError('`uri` does not appear to be a Data URI (must begin with "data:")');
  }
  uri = uri.replace(/\r?\n/g, "");
  const firstComma = uri.indexOf(",");
  if (firstComma === -1 || firstComma <= 4) {
    throw new TypeError("malformed data: URI");
  }
  const meta = uri.substring(5, firstComma).split(";");
  let charset = "";
  let base64 = false;
  const type = meta[0] || "text/plain";
  let typeFull = type;
  for (let i = 1; i < meta.length; i++) {
    if (meta[i] === "base64") {
      base64 = true;
    } else {
      typeFull += `;${meta[i]}`;
      if (meta[i].indexOf("charset=") === 0) {
        charset = meta[i].substring(8);
      }
    }
  }
  if (!meta[0] && !charset.length) {
    typeFull += ";charset=US-ASCII";
    charset = "US-ASCII";
  }
  const encoding = base64 ? "base64" : "ascii";
  const data = unescape(uri.substring(firstComma + 1));
  const buffer = Buffer.from(data, encoding);
  buffer.type = type;
  buffer.typeFull = typeFull;
  buffer.charset = charset;
  return buffer;
}
var src = dataUriToBuffer;
const {Readable} = Stream;
const wm = new WeakMap();
async function* read(parts) {
  for (const part of parts) {
    if ("stream" in part) {
      yield* part.stream();
    } else {
      yield part;
    }
  }
}
class Blob {
  constructor(blobParts = [], options = {type: ""}) {
    let size = 0;
    const parts = blobParts.map((element) => {
      let buffer;
      if (element instanceof Buffer) {
        buffer = element;
      } else if (ArrayBuffer.isView(element)) {
        buffer = Buffer.from(element.buffer, element.byteOffset, element.byteLength);
      } else if (element instanceof ArrayBuffer) {
        buffer = Buffer.from(element);
      } else if (element instanceof Blob) {
        buffer = element;
      } else {
        buffer = Buffer.from(typeof element === "string" ? element : String(element));
      }
      size += buffer.length || buffer.size || 0;
      return buffer;
    });
    const type = options.type === void 0 ? "" : String(options.type).toLowerCase();
    wm.set(this, {
      type: /[^\u0020-\u007E]/.test(type) ? "" : type,
      size,
      parts
    });
  }
  get size() {
    return wm.get(this).size;
  }
  get type() {
    return wm.get(this).type;
  }
  async text() {
    return Buffer.from(await this.arrayBuffer()).toString();
  }
  async arrayBuffer() {
    const data = new Uint8Array(this.size);
    let offset = 0;
    for await (const chunk of this.stream()) {
      data.set(chunk, offset);
      offset += chunk.length;
    }
    return data.buffer;
  }
  stream() {
    return Readable.from(read(wm.get(this).parts));
  }
  slice(start = 0, end = this.size, type = "") {
    const {size} = this;
    let relativeStart = start < 0 ? Math.max(size + start, 0) : Math.min(start, size);
    let relativeEnd = end < 0 ? Math.max(size + end, 0) : Math.min(end, size);
    const span = Math.max(relativeEnd - relativeStart, 0);
    const parts = wm.get(this).parts.values();
    const blobParts = [];
    let added = 0;
    for (const part of parts) {
      const size2 = ArrayBuffer.isView(part) ? part.byteLength : part.size;
      if (relativeStart && size2 <= relativeStart) {
        relativeStart -= size2;
        relativeEnd -= size2;
      } else {
        const chunk = part.slice(relativeStart, Math.min(size2, relativeEnd));
        blobParts.push(chunk);
        added += ArrayBuffer.isView(chunk) ? chunk.byteLength : chunk.size;
        relativeStart = 0;
        if (added >= span) {
          break;
        }
      }
    }
    const blob = new Blob([], {type});
    Object.assign(wm.get(blob), {size: span, parts: blobParts});
    return blob;
  }
  get [Symbol.toStringTag]() {
    return "Blob";
  }
  static [Symbol.hasInstance](object) {
    return typeof object === "object" && typeof object.stream === "function" && object.stream.length === 0 && typeof object.constructor === "function" && /^(Blob|File)$/.test(object[Symbol.toStringTag]);
  }
}
Object.defineProperties(Blob.prototype, {
  size: {enumerable: true},
  type: {enumerable: true},
  slice: {enumerable: true}
});
var fetchBlob = Blob;
class FetchBaseError extends Error {
  constructor(message, type) {
    super(message);
    Error.captureStackTrace(this, this.constructor);
    this.type = type;
  }
  get name() {
    return this.constructor.name;
  }
  get [Symbol.toStringTag]() {
    return this.constructor.name;
  }
}
class FetchError extends FetchBaseError {
  constructor(message, type, systemError) {
    super(message, type);
    if (systemError) {
      this.code = this.errno = systemError.code;
      this.erroredSysCall = systemError.syscall;
    }
  }
}
const NAME = Symbol.toStringTag;
const isURLSearchParameters = (object) => {
  return typeof object === "object" && typeof object.append === "function" && typeof object.delete === "function" && typeof object.get === "function" && typeof object.getAll === "function" && typeof object.has === "function" && typeof object.set === "function" && typeof object.sort === "function" && object[NAME] === "URLSearchParams";
};
const isBlob = (object) => {
  return typeof object === "object" && typeof object.arrayBuffer === "function" && typeof object.type === "string" && typeof object.stream === "function" && typeof object.constructor === "function" && /^(Blob|File)$/.test(object[NAME]);
};
function isFormData(object) {
  return typeof object === "object" && typeof object.append === "function" && typeof object.set === "function" && typeof object.get === "function" && typeof object.getAll === "function" && typeof object.delete === "function" && typeof object.keys === "function" && typeof object.values === "function" && typeof object.entries === "function" && typeof object.constructor === "function" && object[NAME] === "FormData";
}
const isAbortSignal = (object) => {
  return typeof object === "object" && object[NAME] === "AbortSignal";
};
const carriage = "\r\n";
const dashes = "-".repeat(2);
const carriageLength = Buffer.byteLength(carriage);
const getFooter = (boundary) => `${dashes}${boundary}${dashes}${carriage.repeat(2)}`;
function getHeader(boundary, name, field) {
  let header = "";
  header += `${dashes}${boundary}${carriage}`;
  header += `Content-Disposition: form-data; name="${name}"`;
  if (isBlob(field)) {
    header += `; filename="${field.name}"${carriage}`;
    header += `Content-Type: ${field.type || "application/octet-stream"}`;
  }
  return `${header}${carriage.repeat(2)}`;
}
const getBoundary = () => randomBytes(8).toString("hex");
async function* formDataIterator(form, boundary) {
  for (const [name, value] of form) {
    yield getHeader(boundary, name, value);
    if (isBlob(value)) {
      yield* value.stream();
    } else {
      yield value;
    }
    yield carriage;
  }
  yield getFooter(boundary);
}
function getFormDataLength(form, boundary) {
  let length = 0;
  for (const [name, value] of form) {
    length += Buffer.byteLength(getHeader(boundary, name, value));
    if (isBlob(value)) {
      length += value.size;
    } else {
      length += Buffer.byteLength(String(value));
    }
    length += carriageLength;
  }
  length += Buffer.byteLength(getFooter(boundary));
  return length;
}
const INTERNALS$2 = Symbol("Body internals");
class Body {
  constructor(body, {
    size = 0
  } = {}) {
    let boundary = null;
    if (body === null) {
      body = null;
    } else if (isURLSearchParameters(body)) {
      body = Buffer.from(body.toString());
    } else if (isBlob(body))
      ;
    else if (Buffer.isBuffer(body))
      ;
    else if (types.isAnyArrayBuffer(body)) {
      body = Buffer.from(body);
    } else if (ArrayBuffer.isView(body)) {
      body = Buffer.from(body.buffer, body.byteOffset, body.byteLength);
    } else if (body instanceof Stream)
      ;
    else if (isFormData(body)) {
      boundary = `NodeFetchFormDataBoundary${getBoundary()}`;
      body = Stream.Readable.from(formDataIterator(body, boundary));
    } else {
      body = Buffer.from(String(body));
    }
    this[INTERNALS$2] = {
      body,
      boundary,
      disturbed: false,
      error: null
    };
    this.size = size;
    if (body instanceof Stream) {
      body.on("error", (err) => {
        const error2 = err instanceof FetchBaseError ? err : new FetchError(`Invalid response body while trying to fetch ${this.url}: ${err.message}`, "system", err);
        this[INTERNALS$2].error = error2;
      });
    }
  }
  get body() {
    return this[INTERNALS$2].body;
  }
  get bodyUsed() {
    return this[INTERNALS$2].disturbed;
  }
  async arrayBuffer() {
    const {buffer, byteOffset, byteLength} = await consumeBody(this);
    return buffer.slice(byteOffset, byteOffset + byteLength);
  }
  async blob() {
    const ct = this.headers && this.headers.get("content-type") || this[INTERNALS$2].body && this[INTERNALS$2].body.type || "";
    const buf = await this.buffer();
    return new fetchBlob([buf], {
      type: ct
    });
  }
  async json() {
    const buffer = await consumeBody(this);
    return JSON.parse(buffer.toString());
  }
  async text() {
    const buffer = await consumeBody(this);
    return buffer.toString();
  }
  buffer() {
    return consumeBody(this);
  }
}
Object.defineProperties(Body.prototype, {
  body: {enumerable: true},
  bodyUsed: {enumerable: true},
  arrayBuffer: {enumerable: true},
  blob: {enumerable: true},
  json: {enumerable: true},
  text: {enumerable: true}
});
async function consumeBody(data) {
  if (data[INTERNALS$2].disturbed) {
    throw new TypeError(`body used already for: ${data.url}`);
  }
  data[INTERNALS$2].disturbed = true;
  if (data[INTERNALS$2].error) {
    throw data[INTERNALS$2].error;
  }
  let {body} = data;
  if (body === null) {
    return Buffer.alloc(0);
  }
  if (isBlob(body)) {
    body = body.stream();
  }
  if (Buffer.isBuffer(body)) {
    return body;
  }
  if (!(body instanceof Stream)) {
    return Buffer.alloc(0);
  }
  const accum = [];
  let accumBytes = 0;
  try {
    for await (const chunk of body) {
      if (data.size > 0 && accumBytes + chunk.length > data.size) {
        const err = new FetchError(`content size at ${data.url} over limit: ${data.size}`, "max-size");
        body.destroy(err);
        throw err;
      }
      accumBytes += chunk.length;
      accum.push(chunk);
    }
  } catch (error2) {
    if (error2 instanceof FetchBaseError) {
      throw error2;
    } else {
      throw new FetchError(`Invalid response body while trying to fetch ${data.url}: ${error2.message}`, "system", error2);
    }
  }
  if (body.readableEnded === true || body._readableState.ended === true) {
    try {
      if (accum.every((c) => typeof c === "string")) {
        return Buffer.from(accum.join(""));
      }
      return Buffer.concat(accum, accumBytes);
    } catch (error2) {
      throw new FetchError(`Could not create Buffer from response body for ${data.url}: ${error2.message}`, "system", error2);
    }
  } else {
    throw new FetchError(`Premature close of server response while trying to fetch ${data.url}`);
  }
}
const clone = (instance, highWaterMark) => {
  let p1;
  let p2;
  let {body} = instance;
  if (instance.bodyUsed) {
    throw new Error("cannot clone body after it is used");
  }
  if (body instanceof Stream && typeof body.getBoundary !== "function") {
    p1 = new PassThrough({highWaterMark});
    p2 = new PassThrough({highWaterMark});
    body.pipe(p1);
    body.pipe(p2);
    instance[INTERNALS$2].body = p1;
    body = p2;
  }
  return body;
};
const extractContentType = (body, request) => {
  if (body === null) {
    return null;
  }
  if (typeof body === "string") {
    return "text/plain;charset=UTF-8";
  }
  if (isURLSearchParameters(body)) {
    return "application/x-www-form-urlencoded;charset=UTF-8";
  }
  if (isBlob(body)) {
    return body.type || null;
  }
  if (Buffer.isBuffer(body) || types.isAnyArrayBuffer(body) || ArrayBuffer.isView(body)) {
    return null;
  }
  if (body && typeof body.getBoundary === "function") {
    return `multipart/form-data;boundary=${body.getBoundary()}`;
  }
  if (isFormData(body)) {
    return `multipart/form-data; boundary=${request[INTERNALS$2].boundary}`;
  }
  if (body instanceof Stream) {
    return null;
  }
  return "text/plain;charset=UTF-8";
};
const getTotalBytes = (request) => {
  const {body} = request;
  if (body === null) {
    return 0;
  }
  if (isBlob(body)) {
    return body.size;
  }
  if (Buffer.isBuffer(body)) {
    return body.length;
  }
  if (body && typeof body.getLengthSync === "function") {
    return body.hasKnownLength && body.hasKnownLength() ? body.getLengthSync() : null;
  }
  if (isFormData(body)) {
    return getFormDataLength(request[INTERNALS$2].boundary);
  }
  return null;
};
const writeToStream = (dest, {body}) => {
  if (body === null) {
    dest.end();
  } else if (isBlob(body)) {
    body.stream().pipe(dest);
  } else if (Buffer.isBuffer(body)) {
    dest.write(body);
    dest.end();
  } else {
    body.pipe(dest);
  }
};
const validateHeaderName = typeof http.validateHeaderName === "function" ? http.validateHeaderName : (name) => {
  if (!/^[\^`\-\w!#$%&'*+.|~]+$/.test(name)) {
    const err = new TypeError(`Header name must be a valid HTTP token [${name}]`);
    Object.defineProperty(err, "code", {value: "ERR_INVALID_HTTP_TOKEN"});
    throw err;
  }
};
const validateHeaderValue = typeof http.validateHeaderValue === "function" ? http.validateHeaderValue : (name, value) => {
  if (/[^\t\u0020-\u007E\u0080-\u00FF]/.test(value)) {
    const err = new TypeError(`Invalid character in header content ["${name}"]`);
    Object.defineProperty(err, "code", {value: "ERR_INVALID_CHAR"});
    throw err;
  }
};
class Headers extends URLSearchParams {
  constructor(init2) {
    let result = [];
    if (init2 instanceof Headers) {
      const raw = init2.raw();
      for (const [name, values] of Object.entries(raw)) {
        result.push(...values.map((value) => [name, value]));
      }
    } else if (init2 == null)
      ;
    else if (typeof init2 === "object" && !types.isBoxedPrimitive(init2)) {
      const method = init2[Symbol.iterator];
      if (method == null) {
        result.push(...Object.entries(init2));
      } else {
        if (typeof method !== "function") {
          throw new TypeError("Header pairs must be iterable");
        }
        result = [...init2].map((pair) => {
          if (typeof pair !== "object" || types.isBoxedPrimitive(pair)) {
            throw new TypeError("Each header pair must be an iterable object");
          }
          return [...pair];
        }).map((pair) => {
          if (pair.length !== 2) {
            throw new TypeError("Each header pair must be a name/value tuple");
          }
          return [...pair];
        });
      }
    } else {
      throw new TypeError("Failed to construct 'Headers': The provided value is not of type '(sequence<sequence<ByteString>> or record<ByteString, ByteString>)");
    }
    result = result.length > 0 ? result.map(([name, value]) => {
      validateHeaderName(name);
      validateHeaderValue(name, String(value));
      return [String(name).toLowerCase(), String(value)];
    }) : void 0;
    super(result);
    return new Proxy(this, {
      get(target, p, receiver) {
        switch (p) {
          case "append":
          case "set":
            return (name, value) => {
              validateHeaderName(name);
              validateHeaderValue(name, String(value));
              return URLSearchParams.prototype[p].call(receiver, String(name).toLowerCase(), String(value));
            };
          case "delete":
          case "has":
          case "getAll":
            return (name) => {
              validateHeaderName(name);
              return URLSearchParams.prototype[p].call(receiver, String(name).toLowerCase());
            };
          case "keys":
            return () => {
              target.sort();
              return new Set(URLSearchParams.prototype.keys.call(target)).keys();
            };
          default:
            return Reflect.get(target, p, receiver);
        }
      }
    });
  }
  get [Symbol.toStringTag]() {
    return this.constructor.name;
  }
  toString() {
    return Object.prototype.toString.call(this);
  }
  get(name) {
    const values = this.getAll(name);
    if (values.length === 0) {
      return null;
    }
    let value = values.join(", ");
    if (/^content-encoding$/i.test(name)) {
      value = value.toLowerCase();
    }
    return value;
  }
  forEach(callback) {
    for (const name of this.keys()) {
      callback(this.get(name), name);
    }
  }
  *values() {
    for (const name of this.keys()) {
      yield this.get(name);
    }
  }
  *entries() {
    for (const name of this.keys()) {
      yield [name, this.get(name)];
    }
  }
  [Symbol.iterator]() {
    return this.entries();
  }
  raw() {
    return [...this.keys()].reduce((result, key) => {
      result[key] = this.getAll(key);
      return result;
    }, {});
  }
  [Symbol.for("nodejs.util.inspect.custom")]() {
    return [...this.keys()].reduce((result, key) => {
      const values = this.getAll(key);
      if (key === "host") {
        result[key] = values[0];
      } else {
        result[key] = values.length > 1 ? values : values[0];
      }
      return result;
    }, {});
  }
}
Object.defineProperties(Headers.prototype, ["get", "entries", "forEach", "values"].reduce((result, property) => {
  result[property] = {enumerable: true};
  return result;
}, {}));
function fromRawHeaders(headers = []) {
  return new Headers(headers.reduce((result, value, index2, array) => {
    if (index2 % 2 === 0) {
      result.push(array.slice(index2, index2 + 2));
    }
    return result;
  }, []).filter(([name, value]) => {
    try {
      validateHeaderName(name);
      validateHeaderValue(name, String(value));
      return true;
    } catch (e) {
      return false;
    }
  }));
}
const redirectStatus = new Set([301, 302, 303, 307, 308]);
const isRedirect = (code) => {
  return redirectStatus.has(code);
};
const INTERNALS$1 = Symbol("Response internals");
class Response extends Body {
  constructor(body = null, options = {}) {
    super(body, options);
    const status = options.status || 200;
    const headers = new Headers(options.headers);
    if (body !== null && !headers.has("Content-Type")) {
      const contentType = extractContentType(body);
      if (contentType) {
        headers.append("Content-Type", contentType);
      }
    }
    this[INTERNALS$1] = {
      url: options.url,
      status,
      statusText: options.statusText || "",
      headers,
      counter: options.counter,
      highWaterMark: options.highWaterMark
    };
  }
  get url() {
    return this[INTERNALS$1].url || "";
  }
  get status() {
    return this[INTERNALS$1].status;
  }
  get ok() {
    return this[INTERNALS$1].status >= 200 && this[INTERNALS$1].status < 300;
  }
  get redirected() {
    return this[INTERNALS$1].counter > 0;
  }
  get statusText() {
    return this[INTERNALS$1].statusText;
  }
  get headers() {
    return this[INTERNALS$1].headers;
  }
  get highWaterMark() {
    return this[INTERNALS$1].highWaterMark;
  }
  clone() {
    return new Response(clone(this, this.highWaterMark), {
      url: this.url,
      status: this.status,
      statusText: this.statusText,
      headers: this.headers,
      ok: this.ok,
      redirected: this.redirected,
      size: this.size
    });
  }
  static redirect(url, status = 302) {
    if (!isRedirect(status)) {
      throw new RangeError('Failed to execute "redirect" on "response": Invalid status code');
    }
    return new Response(null, {
      headers: {
        location: new URL(url).toString()
      },
      status
    });
  }
  get [Symbol.toStringTag]() {
    return "Response";
  }
}
Object.defineProperties(Response.prototype, {
  url: {enumerable: true},
  status: {enumerable: true},
  ok: {enumerable: true},
  redirected: {enumerable: true},
  statusText: {enumerable: true},
  headers: {enumerable: true},
  clone: {enumerable: true}
});
const getSearch = (parsedURL) => {
  if (parsedURL.search) {
    return parsedURL.search;
  }
  const lastOffset = parsedURL.href.length - 1;
  const hash = parsedURL.hash || (parsedURL.href[lastOffset] === "#" ? "#" : "");
  return parsedURL.href[lastOffset - hash.length] === "?" ? "?" : "";
};
const INTERNALS = Symbol("Request internals");
const isRequest = (object) => {
  return typeof object === "object" && typeof object[INTERNALS] === "object";
};
class Request extends Body {
  constructor(input, init2 = {}) {
    let parsedURL;
    if (isRequest(input)) {
      parsedURL = new URL(input.url);
    } else {
      parsedURL = new URL(input);
      input = {};
    }
    let method = init2.method || input.method || "GET";
    method = method.toUpperCase();
    if ((init2.body != null || isRequest(input)) && input.body !== null && (method === "GET" || method === "HEAD")) {
      throw new TypeError("Request with GET/HEAD method cannot have body");
    }
    const inputBody = init2.body ? init2.body : isRequest(input) && input.body !== null ? clone(input) : null;
    super(inputBody, {
      size: init2.size || input.size || 0
    });
    const headers = new Headers(init2.headers || input.headers || {});
    if (inputBody !== null && !headers.has("Content-Type")) {
      const contentType = extractContentType(inputBody, this);
      if (contentType) {
        headers.append("Content-Type", contentType);
      }
    }
    let signal = isRequest(input) ? input.signal : null;
    if ("signal" in init2) {
      signal = init2.signal;
    }
    if (signal !== null && !isAbortSignal(signal)) {
      throw new TypeError("Expected signal to be an instanceof AbortSignal");
    }
    this[INTERNALS] = {
      method,
      redirect: init2.redirect || input.redirect || "follow",
      headers,
      parsedURL,
      signal
    };
    this.follow = init2.follow === void 0 ? input.follow === void 0 ? 20 : input.follow : init2.follow;
    this.compress = init2.compress === void 0 ? input.compress === void 0 ? true : input.compress : init2.compress;
    this.counter = init2.counter || input.counter || 0;
    this.agent = init2.agent || input.agent;
    this.highWaterMark = init2.highWaterMark || input.highWaterMark || 16384;
    this.insecureHTTPParser = init2.insecureHTTPParser || input.insecureHTTPParser || false;
  }
  get method() {
    return this[INTERNALS].method;
  }
  get url() {
    return format(this[INTERNALS].parsedURL);
  }
  get headers() {
    return this[INTERNALS].headers;
  }
  get redirect() {
    return this[INTERNALS].redirect;
  }
  get signal() {
    return this[INTERNALS].signal;
  }
  clone() {
    return new Request(this);
  }
  get [Symbol.toStringTag]() {
    return "Request";
  }
}
Object.defineProperties(Request.prototype, {
  method: {enumerable: true},
  url: {enumerable: true},
  headers: {enumerable: true},
  redirect: {enumerable: true},
  clone: {enumerable: true},
  signal: {enumerable: true}
});
const getNodeRequestOptions = (request) => {
  const {parsedURL} = request[INTERNALS];
  const headers = new Headers(request[INTERNALS].headers);
  if (!headers.has("Accept")) {
    headers.set("Accept", "*/*");
  }
  let contentLengthValue = null;
  if (request.body === null && /^(post|put)$/i.test(request.method)) {
    contentLengthValue = "0";
  }
  if (request.body !== null) {
    const totalBytes = getTotalBytes(request);
    if (typeof totalBytes === "number" && !Number.isNaN(totalBytes)) {
      contentLengthValue = String(totalBytes);
    }
  }
  if (contentLengthValue) {
    headers.set("Content-Length", contentLengthValue);
  }
  if (!headers.has("User-Agent")) {
    headers.set("User-Agent", "node-fetch");
  }
  if (request.compress && !headers.has("Accept-Encoding")) {
    headers.set("Accept-Encoding", "gzip,deflate,br");
  }
  let {agent} = request;
  if (typeof agent === "function") {
    agent = agent(parsedURL);
  }
  if (!headers.has("Connection") && !agent) {
    headers.set("Connection", "close");
  }
  const search = getSearch(parsedURL);
  const requestOptions = {
    path: parsedURL.pathname + search,
    pathname: parsedURL.pathname,
    hostname: parsedURL.hostname,
    protocol: parsedURL.protocol,
    port: parsedURL.port,
    hash: parsedURL.hash,
    search: parsedURL.search,
    query: parsedURL.query,
    href: parsedURL.href,
    method: request.method,
    headers: headers[Symbol.for("nodejs.util.inspect.custom")](),
    insecureHTTPParser: request.insecureHTTPParser,
    agent
  };
  return requestOptions;
};
class AbortError extends FetchBaseError {
  constructor(message, type = "aborted") {
    super(message, type);
  }
}
const supportedSchemas = new Set(["data:", "http:", "https:"]);
async function fetch(url, options_) {
  return new Promise((resolve2, reject) => {
    const request = new Request(url, options_);
    const options = getNodeRequestOptions(request);
    if (!supportedSchemas.has(options.protocol)) {
      throw new TypeError(`node-fetch cannot load ${url}. URL scheme "${options.protocol.replace(/:$/, "")}" is not supported.`);
    }
    if (options.protocol === "data:") {
      const data = src(request.url);
      const response2 = new Response(data, {headers: {"Content-Type": data.typeFull}});
      resolve2(response2);
      return;
    }
    const send = (options.protocol === "https:" ? https : http).request;
    const {signal} = request;
    let response = null;
    const abort = () => {
      const error2 = new AbortError("The operation was aborted.");
      reject(error2);
      if (request.body && request.body instanceof Stream.Readable) {
        request.body.destroy(error2);
      }
      if (!response || !response.body) {
        return;
      }
      response.body.emit("error", error2);
    };
    if (signal && signal.aborted) {
      abort();
      return;
    }
    const abortAndFinalize = () => {
      abort();
      finalize();
    };
    const request_ = send(options);
    if (signal) {
      signal.addEventListener("abort", abortAndFinalize);
    }
    const finalize = () => {
      request_.abort();
      if (signal) {
        signal.removeEventListener("abort", abortAndFinalize);
      }
    };
    request_.on("error", (err) => {
      reject(new FetchError(`request to ${request.url} failed, reason: ${err.message}`, "system", err));
      finalize();
    });
    request_.on("response", (response_) => {
      request_.setTimeout(0);
      const headers = fromRawHeaders(response_.rawHeaders);
      if (isRedirect(response_.statusCode)) {
        const location = headers.get("Location");
        const locationURL = location === null ? null : new URL(location, request.url);
        switch (request.redirect) {
          case "error":
            reject(new FetchError(`uri requested responds with a redirect, redirect mode is set to error: ${request.url}`, "no-redirect"));
            finalize();
            return;
          case "manual":
            if (locationURL !== null) {
              try {
                headers.set("Location", locationURL);
              } catch (error2) {
                reject(error2);
              }
            }
            break;
          case "follow": {
            if (locationURL === null) {
              break;
            }
            if (request.counter >= request.follow) {
              reject(new FetchError(`maximum redirect reached at: ${request.url}`, "max-redirect"));
              finalize();
              return;
            }
            const requestOptions = {
              headers: new Headers(request.headers),
              follow: request.follow,
              counter: request.counter + 1,
              agent: request.agent,
              compress: request.compress,
              method: request.method,
              body: request.body,
              signal: request.signal,
              size: request.size
            };
            if (response_.statusCode !== 303 && request.body && options_.body instanceof Stream.Readable) {
              reject(new FetchError("Cannot follow redirect with body being a readable stream", "unsupported-redirect"));
              finalize();
              return;
            }
            if (response_.statusCode === 303 || (response_.statusCode === 301 || response_.statusCode === 302) && request.method === "POST") {
              requestOptions.method = "GET";
              requestOptions.body = void 0;
              requestOptions.headers.delete("content-length");
            }
            resolve2(fetch(new Request(locationURL, requestOptions)));
            finalize();
            return;
          }
        }
      }
      response_.once("end", () => {
        if (signal) {
          signal.removeEventListener("abort", abortAndFinalize);
        }
      });
      let body = pipeline(response_, new PassThrough(), (error2) => {
        reject(error2);
      });
      if (process.version < "v12.10") {
        response_.on("aborted", abortAndFinalize);
      }
      const responseOptions = {
        url: request.url,
        status: response_.statusCode,
        statusText: response_.statusMessage,
        headers,
        size: request.size,
        counter: request.counter,
        highWaterMark: request.highWaterMark
      };
      const codings = headers.get("Content-Encoding");
      if (!request.compress || request.method === "HEAD" || codings === null || response_.statusCode === 204 || response_.statusCode === 304) {
        response = new Response(body, responseOptions);
        resolve2(response);
        return;
      }
      const zlibOptions = {
        flush: zlib.Z_SYNC_FLUSH,
        finishFlush: zlib.Z_SYNC_FLUSH
      };
      if (codings === "gzip" || codings === "x-gzip") {
        body = pipeline(body, zlib.createGunzip(zlibOptions), (error2) => {
          reject(error2);
        });
        response = new Response(body, responseOptions);
        resolve2(response);
        return;
      }
      if (codings === "deflate" || codings === "x-deflate") {
        const raw = pipeline(response_, new PassThrough(), (error2) => {
          reject(error2);
        });
        raw.once("data", (chunk) => {
          if ((chunk[0] & 15) === 8) {
            body = pipeline(body, zlib.createInflate(), (error2) => {
              reject(error2);
            });
          } else {
            body = pipeline(body, zlib.createInflateRaw(), (error2) => {
              reject(error2);
            });
          }
          response = new Response(body, responseOptions);
          resolve2(response);
        });
        return;
      }
      if (codings === "br") {
        body = pipeline(body, zlib.createBrotliDecompress(), (error2) => {
          reject(error2);
        });
        response = new Response(body, responseOptions);
        resolve2(response);
        return;
      }
      response = new Response(body, responseOptions);
      resolve2(response);
    });
    writeToStream(request_, request);
  });
}
function normalize(loaded) {
  if (loaded.error) {
    const error2 = typeof loaded.error === "string" ? new Error(loaded.error) : loaded.error;
    const status = loaded.status;
    if (!(error2 instanceof Error)) {
      return {
        status: 500,
        error: new Error(`"error" property returned from load() must be a string or instance of Error, received type "${typeof error2}"`)
      };
    }
    if (!status || status < 400 || status > 599) {
      console.warn('"error" returned from load() without a valid status code \u2014 defaulting to 500');
      return {status: 500, error: error2};
    }
    return {status, error: error2};
  }
  if (loaded.redirect) {
    if (!loaded.status || Math.floor(loaded.status / 100) !== 3) {
      return {
        status: 500,
        error: new Error('"redirect" property returned from load() must be accompanied by a 3xx status code')
      };
    }
    if (typeof loaded.redirect !== "string") {
      return {
        status: 500,
        error: new Error('"redirect" property returned from load() must be a string')
      };
    }
  }
  return loaded;
}
const s = JSON.stringify;
async function load_node({
  request,
  options,
  route,
  page,
  node,
  $session,
  context,
  is_leaf,
  is_error,
  status,
  error: error2
}) {
  const {module} = node;
  let uses_credentials = false;
  const fetched = [];
  let loaded;
  if (module.load) {
    const load_input = {
      page,
      get session() {
        uses_credentials = true;
        return $session;
      },
      fetch: async (resource, opts = {}) => {
        let url;
        if (typeof resource === "string") {
          url = resource;
        } else {
          url = resource.url;
          opts = {
            method: resource.method,
            headers: resource.headers,
            body: resource.body,
            mode: resource.mode,
            credentials: resource.credentials,
            cache: resource.cache,
            redirect: resource.redirect,
            referrer: resource.referrer,
            integrity: resource.integrity,
            ...opts
          };
        }
        if (options.local && url.startsWith(options.paths.assets)) {
          url = url.replace(options.paths.assets, "");
        }
        const parsed = parse(url);
        let response;
        if (parsed.protocol) {
          response = await fetch(parsed.href, opts);
        } else {
          const resolved = resolve(request.path, parsed.pathname);
          const filename = resolved.slice(1);
          const filename_html = `${filename}/index.html`;
          const asset = options.manifest.assets.find((d) => d.file === filename || d.file === filename_html);
          if (asset) {
            if (options.get_static_file) {
              response = new Response(options.get_static_file(asset.file), {
                headers: {
                  "content-type": asset.type
                }
              });
            } else {
              response = await fetch(`http://${page.host}/${asset.file}`, opts);
            }
          }
          if (!response) {
            const headers = {...opts.headers};
            if (opts.credentials !== "omit") {
              uses_credentials = true;
              headers.cookie = request.headers.cookie;
              if (!headers.authorization) {
                headers.authorization = request.headers.authorization;
              }
            }
            const rendered = await ssr({
              host: request.host,
              method: opts.method || "GET",
              headers,
              path: resolved,
              body: opts.body,
              query: new URLSearchParams(parsed.query || "")
            }, {
              ...options,
              fetched: url,
              initiator: route
            });
            if (rendered) {
              if (options.dependencies) {
                options.dependencies.set(resolved, rendered);
              }
              response = new Response(rendered.body, {
                status: rendered.status,
                headers: rendered.headers
              });
            }
          }
        }
        if (response) {
          const proxy = new Proxy(response, {
            get(response2, key, receiver) {
              async function text() {
                const body = await response2.text();
                const headers = {};
                response2.headers.forEach((value, key2) => {
                  if (key2 !== "etag" && key2 !== "set-cookie")
                    headers[key2] = value;
                });
                fetched.push({
                  url,
                  json: `{"status":${response2.status},"statusText":${s(response2.statusText)},"headers":${s(headers)},"body":${escape$1(body)}}`
                });
                return body;
              }
              if (key === "text") {
                return text;
              }
              if (key === "json") {
                return async () => {
                  return JSON.parse(await text());
                };
              }
              return Reflect.get(response2, key, receiver);
            }
          });
          return proxy;
        }
        return response || new Response("Not found", {
          status: 404
        });
      },
      context: {...context}
    };
    if (is_error) {
      load_input.status = status;
      load_input.error = error2;
    }
    loaded = await module.load.call(null, load_input);
  } else {
    loaded = {};
  }
  if (!loaded && is_leaf && !is_error)
    return;
  return {
    node,
    loaded: normalize(loaded),
    context: loaded.context || context,
    fetched,
    uses_credentials
  };
}
const escaped$2 = {
  "<": "\\u003C",
  ">": "\\u003E",
  "/": "\\u002F",
  "\\": "\\\\",
  "\b": "\\b",
  "\f": "\\f",
  "\n": "\\n",
  "\r": "\\r",
  "	": "\\t",
  "\0": "\\0",
  "\u2028": "\\u2028",
  "\u2029": "\\u2029"
};
function escape$1(str) {
  let result = '"';
  for (let i = 0; i < str.length; i += 1) {
    const char = str.charAt(i);
    const code = char.charCodeAt(0);
    if (char === '"') {
      result += '\\"';
    } else if (char in escaped$2) {
      result += escaped$2[char];
    } else if (code >= 55296 && code <= 57343) {
      const next = str.charCodeAt(i + 1);
      if (code <= 56319 && next >= 56320 && next <= 57343) {
        result += char + str[++i];
      } else {
        result += `\\u${code.toString(16).toUpperCase()}`;
      }
    } else {
      result += char;
    }
  }
  result += '"';
  return result;
}
async function respond_with_error({request, options, $session, status, error: error2}) {
  const default_layout = await options.load_component(options.manifest.layout);
  const default_error = await options.load_component(options.manifest.error);
  const page = {
    host: request.host,
    path: request.path,
    query: request.query,
    params: {}
  };
  const loaded = await load_node({
    request,
    options,
    route: null,
    page,
    node: default_layout,
    $session,
    context: {},
    is_leaf: false,
    is_error: false
  });
  const branch = [
    loaded,
    await load_node({
      request,
      options,
      route: null,
      page,
      node: default_error,
      $session,
      context: loaded.context,
      is_leaf: false,
      is_error: true,
      status,
      error: error2
    })
  ];
  try {
    return await render_response({
      request,
      options,
      $session,
      page_config: {
        hydrate: options.hydrate,
        router: options.router,
        ssr: options.ssr
      },
      status,
      error: error2,
      branch,
      page
    });
  } catch (error3) {
    return {
      status: 500,
      headers: {},
      body: options.dev ? error3.stack : error3.message
    };
  }
}
async function respond({request, options, $session, route}) {
  const match = route.pattern.exec(request.path);
  const params = route.params(match);
  const page = {
    host: request.host,
    path: request.path,
    query: request.query,
    params
  };
  let nodes;
  try {
    nodes = await Promise.all(route.a.map((id) => id && options.load_component(id)));
  } catch (error3) {
    return await respond_with_error({
      request,
      options,
      $session,
      status: 500,
      error: error3
    });
  }
  const leaf = nodes[nodes.length - 1].module;
  const page_config = {
    ssr: "ssr" in leaf ? leaf.ssr : options.ssr,
    router: "router" in leaf ? leaf.router : options.router,
    hydrate: "hydrate" in leaf ? leaf.hydrate : options.hydrate
  };
  if (options.only_render_prerenderable_pages && !leaf.prerender) {
    return {
      status: 204,
      headers: {},
      body: null
    };
  }
  let branch;
  let status = 200;
  let error2;
  ssr:
    if (page_config.ssr) {
      let context = {};
      branch = [];
      for (let i = 0; i < nodes.length; i += 1) {
        const node = nodes[i];
        let loaded;
        if (node) {
          try {
            loaded = await load_node({
              request,
              options,
              route,
              page,
              node,
              $session,
              context,
              is_leaf: i === nodes.length - 1,
              is_error: false
            });
            if (!loaded)
              return;
            if (loaded.loaded.redirect) {
              return {
                status: loaded.loaded.status,
                headers: {
                  location: loaded.loaded.redirect
                }
              };
            }
            if (loaded.loaded.error) {
              ({status, error: error2} = loaded.loaded);
            }
          } catch (e) {
            status = 500;
            error2 = e;
          }
          if (error2) {
            while (i--) {
              if (route.b[i]) {
                const error_node = await options.load_component(route.b[i]);
                let error_loaded;
                let node_loaded;
                let j = i;
                while (!(node_loaded = branch[j])) {
                  j -= 1;
                }
                try {
                  error_loaded = await load_node({
                    request,
                    options,
                    route,
                    page,
                    node: error_node,
                    $session,
                    context: node_loaded.context,
                    is_leaf: false,
                    is_error: true,
                    status,
                    error: error2
                  });
                  if (error_loaded.loaded.error) {
                    continue;
                  }
                  branch = branch.slice(0, j + 1).concat(error_loaded);
                  break ssr;
                } catch (e) {
                  continue;
                }
              }
            }
            return await respond_with_error({
              request,
              options,
              $session,
              status,
              error: error2
            });
          }
        }
        branch.push(loaded);
        if (loaded && loaded.loaded.context) {
          context = {
            ...context,
            ...loaded.loaded.context
          };
        }
      }
    }
  try {
    return await render_response({
      request,
      options,
      $session,
      page_config,
      status,
      error: error2,
      branch: branch && branch.filter(Boolean),
      page
    });
  } catch (error3) {
    return await respond_with_error({
      request,
      options,
      $session,
      status: 500,
      error: error3
    });
  }
}
async function render_page(request, route, options) {
  if (options.initiator === route) {
    return {
      status: 404,
      headers: {},
      body: `Not found: ${request.path}`
    };
  }
  const $session = await options.hooks.getSession({context: request.context});
  if (route) {
    const response = await respond({
      request,
      options,
      $session,
      route
    });
    if (response) {
      return response;
    }
    if (options.fetched) {
      return {
        status: 500,
        headers: {},
        body: `Bad request in load function: failed to fetch ${options.fetched}`
      };
    }
  } else {
    return await respond_with_error({
      request,
      options,
      $session,
      status: 404,
      error: new Error(`Not found: ${request.path}`)
    });
  }
}
async function render_route(request, route) {
  const mod = await route.load();
  const handler = mod[request.method.toLowerCase().replace("delete", "del")];
  if (handler) {
    const match = route.pattern.exec(request.path);
    const params = route.params(match);
    const response = await handler({...request, params});
    if (response) {
      if (typeof response !== "object" || response.body == null) {
        return {
          status: 500,
          body: `Invalid response from route ${request.path}; ${response.body == null ? "body is missing" : `expected an object, got ${typeof response}`}`,
          headers: {}
        };
      }
      let {status = 200, body, headers = {}} = response;
      headers = lowercase_keys(headers);
      if (typeof body === "object" && !("content-type" in headers) || headers["content-type"] === "application/json") {
        headers = {...headers, "content-type": "application/json"};
        body = JSON.stringify(body);
      }
      return {status, body, headers};
    }
  }
}
function lowercase_keys(obj) {
  const clone2 = {};
  for (const key in obj) {
    clone2[key.toLowerCase()] = obj[key];
  }
  return clone2;
}
function md5(body) {
  return createHash("md5").update(body).digest("hex");
}
async function ssr(incoming, options) {
  if (incoming.path.endsWith("/") && incoming.path !== "/") {
    const q = incoming.query.toString();
    return {
      status: 301,
      headers: {
        location: incoming.path.slice(0, -1) + (q ? `?${q}` : "")
      }
    };
  }
  const context = await options.hooks.getContext(incoming) || {};
  try {
    return await options.hooks.handle({
      request: {
        ...incoming,
        params: null,
        context
      },
      render: async (request) => {
        for (const route of options.manifest.routes) {
          if (!route.pattern.test(request.path))
            continue;
          const response = route.type === "endpoint" ? await render_route(request, route) : await render_page(request, route, options);
          if (response) {
            if (response.status === 200) {
              if (!/(no-store|immutable)/.test(response.headers["cache-control"])) {
                const etag = `"${md5(response.body)}"`;
                if (request.headers["if-none-match"] === etag) {
                  return {
                    status: 304,
                    headers: {},
                    body: null
                  };
                }
                response.headers["etag"] = etag;
              }
            }
            return response;
          }
        }
        return await render_page(request, null, options);
      }
    });
  } catch (e) {
    if (e && e.stack) {
      e.stack = await options.get_stack(e);
    }
    console.error(e && e.stack || e);
    return {
      status: 500,
      headers: {},
      body: options.dev ? e.stack : e.message
    };
  }
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
let current_component;
function set_current_component(component) {
  current_component = component;
}
function get_current_component() {
  if (!current_component)
    throw new Error("Function called outside component initialization");
  return current_component;
}
function onMount(fn) {
  get_current_component().$$.on_mount.push(fn);
}
function afterUpdate(fn) {
  get_current_component().$$.after_update.push(fn);
}
function setContext(key, context) {
  get_current_component().$$.context.set(key, context);
}
const escaped = {
  '"': "&quot;",
  "'": "&#39;",
  "&": "&amp;",
  "<": "&lt;",
  ">": "&gt;"
};
function escape(html) {
  return String(html).replace(/["'&<>]/g, (match) => escaped[match]);
}
function each(items, fn) {
  let str = "";
  for (let i = 0; i < items.length; i += 1) {
    str += fn(items[i], i);
  }
  return str;
}
const missing_component = {
  $$render: () => ""
};
function validate_component(component, name) {
  if (!component || !component.$$render) {
    if (name === "svelte:component")
      name += " this={...}";
    throw new Error(`<${name}> is not a valid SSR component. You may need to review your build config to ensure that dependencies are compiled, rather than imported as pre-compiled modules`);
  }
  return component;
}
let on_destroy;
function create_ssr_component(fn) {
  function $$render(result, props, bindings, slots, context) {
    const parent_component = current_component;
    const $$ = {
      on_destroy,
      context: new Map(parent_component ? parent_component.$$.context : context || []),
      on_mount: [],
      before_update: [],
      after_update: [],
      callbacks: blank_object()
    };
    set_current_component({$$});
    const html = fn(result, props, bindings, slots);
    set_current_component(parent_component);
    return html;
  }
  return {
    render: (props = {}, {$$slots = {}, context = new Map()} = {}) => {
      on_destroy = [];
      const result = {title: "", head: "", css: new Set()};
      const html = $$render(result, props, {}, $$slots, context);
      run_all(on_destroy);
      return {
        html,
        css: {
          code: Array.from(result.css).map((css2) => css2.code).join("\n"),
          map: null
        },
        head: result.title + result.head
      };
    },
    $$render
  };
}

const css$3 = {
  map: `{"version":3,"file":"root.svelte","sources":["root.svelte"],"sourcesContent":["<!-- This file is generated by @sveltejs/kit \u2014 do not edit it! -->\\n<script>\\n\\timport { setContext, afterUpdate, onMount } from 'svelte';\\n\\n\\t// stores\\n\\texport let stores;\\n\\texport let page;\\n\\n\\texport let components;\\n\\texport let props_0 = null;\\n\\texport let props_1 = null;\\n\\texport let props_2 = null;\\n\\n\\tsetContext('__svelte__', stores);\\n\\n\\t$: stores.page.set(page);\\n\\tafterUpdate(stores.page.notify);\\n\\n\\tlet mounted = false;\\n\\tlet navigated = false;\\n\\tlet title = null;\\n\\n\\tonMount(() => {\\n\\t\\tconst unsubscribe = stores.page.subscribe(() => {\\n\\t\\t\\tif (mounted) {\\n\\t\\t\\t\\tnavigated = true;\\n\\t\\t\\t\\ttitle = document.title;\\n\\t\\t\\t}\\n\\t\\t});\\n\\n\\t\\tmounted = true;\\n\\t\\treturn unsubscribe;\\n\\t});\\n</script>\\n\\n<svelte:component this={components[0]} {...(props_0 || {})}>\\n\\t{#if components[1]}\\n\\t\\t<svelte:component this={components[1]} {...(props_1 || {})}>\\n\\t\\t\\t{#if components[2]}\\n\\t\\t\\t\\t<svelte:component this={components[2]} {...(props_2 || {})}/>\\n\\t\\t\\t{/if}\\n\\t\\t</svelte:component>\\n\\t{/if}\\n</svelte:component>\\n\\n{#if mounted}\\n\\t<div id=\\"svelte-announcer\\" aria-live=\\"assertive\\" aria-atomic=\\"true\\">\\n\\t\\t{#if navigated}\\n\\t\\t\\tNavigated to {title}\\n\\t\\t{/if}\\n\\t</div>\\n{/if}\\n\\n<style>#svelte-announcer{position:absolute;left:0;top:0;clip:rect(0 0 0 0);-webkit-clip-path:inset(50%);clip-path:inset(50%);overflow:hidden;white-space:nowrap;width:1px;height:1px}</style>"],"names":[],"mappings":"AAqDO,gCAAiB,CAAC,SAAS,QAAQ,CAAC,KAAK,CAAC,CAAC,IAAI,CAAC,CAAC,KAAK,KAAK,CAAC,CAAC,CAAC,CAAC,CAAC,CAAC,CAAC,CAAC,CAAC,kBAAkB,MAAM,GAAG,CAAC,CAAC,UAAU,MAAM,GAAG,CAAC,CAAC,SAAS,MAAM,CAAC,YAAY,MAAM,CAAC,MAAM,GAAG,CAAC,OAAO,GAAG,CAAC"}`
};
const Root = create_ssr_component(($$result, $$props, $$bindings, slots) => {
  let {stores} = $$props;
  let {page} = $$props;
  let {components} = $$props;
  let {props_0 = null} = $$props;
  let {props_1 = null} = $$props;
  let {props_2 = null} = $$props;
  setContext("__svelte__", stores);
  afterUpdate(stores.page.notify);
  let mounted = false;
  let navigated = false;
  let title = null;
  onMount(() => {
    const unsubscribe = stores.page.subscribe(() => {
      if (mounted) {
        navigated = true;
        title = document.title;
      }
    });
    mounted = true;
    return unsubscribe;
  });
  if ($$props.stores === void 0 && $$bindings.stores && stores !== void 0)
    $$bindings.stores(stores);
  if ($$props.page === void 0 && $$bindings.page && page !== void 0)
    $$bindings.page(page);
  if ($$props.components === void 0 && $$bindings.components && components !== void 0)
    $$bindings.components(components);
  if ($$props.props_0 === void 0 && $$bindings.props_0 && props_0 !== void 0)
    $$bindings.props_0(props_0);
  if ($$props.props_1 === void 0 && $$bindings.props_1 && props_1 !== void 0)
    $$bindings.props_1(props_1);
  if ($$props.props_2 === void 0 && $$bindings.props_2 && props_2 !== void 0)
    $$bindings.props_2(props_2);
  $$result.css.add(css$3);
  {
    stores.page.set(page);
  }
  return `


${validate_component(components[0] || missing_component, "svelte:component").$$render($$result, Object.assign(props_0 || {}), {}, {
    default: () => `${components[1] ? `${validate_component(components[1] || missing_component, "svelte:component").$$render($$result, Object.assign(props_1 || {}), {}, {
      default: () => `${components[2] ? `${validate_component(components[2] || missing_component, "svelte:component").$$render($$result, Object.assign(props_2 || {}), {}, {})}` : ``}`
    })}` : ``}`
  })}

${mounted ? `<div id="${"svelte-announcer"}" aria-live="${"assertive"}" aria-atomic="${"true"}" class="${"svelte-1y31lbn"}">${navigated ? `Navigated to ${escape(title)}` : ``}</div>` : ``}`;
});
var user_hooks = /* @__PURE__ */ Object.freeze({
  __proto__: null,
  [Symbol.toStringTag]: "Module"
});
const template = ({head, body}) => '<!DOCTYPE html>\n<html lang="en">\n	<head>\n		<meta charset="utf-8" />\n		<link rel="icon" href="/bla.ico" />\n		<meta name="viewport" content="width=device-width, initial-scale=1" />\n		' + head + '\n	</head>\n	<body class="dark:bg-gray-800">\n		<div id="svelte">' + body + "</div>\n	</body>\n</html>\n";
function init({paths, prerendering}) {
}
const empty = () => ({});
const manifest = {
  assets: [{file: "bla.ico", size: 318, type: "image/vnd.microsoft.icon"}, {file: "favicon.ico", size: 1150, type: "image/vnd.microsoft.icon"}, {file: "img/original/city.png", size: 9127785, type: "image/png"}, {file: "img/original/dragon.png", size: 10879439, type: "image/png"}, {file: "img/original/fantasy_1.png", size: 7930297, type: "image/png"}, {file: "img/original/retro_background.jpg", size: 8262, type: "image/jpeg"}, {file: "img/retro_background.jpg", size: 40437, type: "image/jpeg"}, {file: "logo.ico", size: 2570, type: "image/vnd.microsoft.icon"}, {file: "logo.png", size: 2406, type: "image/png"}, {file: "logo.svg", size: 8355, type: "image/svg+xml"}, {file: "robots.txt", size: 67, type: "text/plain"}, {file: "tl.ico", size: 318, type: "image/vnd.microsoft.icon"}],
  layout: "src/routes/$layout.svelte",
  error: ".svelte/build/components/error.svelte",
  routes: [
    {
      type: "page",
      pattern: /^\/$/,
      params: empty,
      a: ["src/routes/$layout.svelte", "src/routes/index.svelte"],
      b: [".svelte/build/components/error.svelte"]
    },
    {
      type: "page",
      pattern: /^\/projects\/randominator\/?$/,
      params: empty,
      a: ["src/routes/$layout.svelte", "src/routes/projects/randominator.svelte"],
      b: [".svelte/build/components/error.svelte"]
    },
    {
      type: "page",
      pattern: /^\/about\/?$/,
      params: empty,
      a: ["src/routes/$layout.svelte", "src/routes/about.svelte"],
      b: [".svelte/build/components/error.svelte"]
    },
    {
      type: "page",
      pattern: /^\/music\/autumn\/?$/,
      params: empty,
      a: ["src/routes/$layout.svelte", "src/routes/music/autumn.svelte"],
      b: [".svelte/build/components/error.svelte"]
    },
    {
      type: "page",
      pattern: /^\/music\/?$/,
      params: empty,
      a: ["src/routes/$layout.svelte", "src/routes/music.svelte"],
      b: [".svelte/build/components/error.svelte"]
    }
  ]
};
const get_hooks = (hooks2) => ({
  getContext: hooks2.getContext || (() => ({})),
  getSession: hooks2.getSession || (() => ({})),
  handle: hooks2.handle || (({request, render: render2}) => render2(request))
});
const hooks = get_hooks(user_hooks);
const module_lookup = {
  "src/routes/$layout.svelte": () => Promise.resolve().then(function() {
    return $layout$1;
  }),
  ".svelte/build/components/error.svelte": () => Promise.resolve().then(function() {
    return error;
  }),
  "src/routes/index.svelte": () => Promise.resolve().then(function() {
    return index;
  }),
  "src/routes/projects/randominator.svelte": () => Promise.resolve().then(function() {
    return randominator;
  }),
  "src/routes/about.svelte": () => Promise.resolve().then(function() {
    return about;
  }),
  "src/routes/music/autumn.svelte": () => Promise.resolve().then(function() {
    return autumn;
  }),
  "src/routes/music.svelte": () => Promise.resolve().then(function() {
    return music;
  })
};
const metadata_lookup = {"src/routes/$layout.svelte": {entry: "/./_app/pages\\$layout.svelte-e1cebcad.js", css: ["/./_app/assets/pages\\$layout.svelte-7cadf8e0.css"], js: ["/./_app/pages\\$layout.svelte-e1cebcad.js", "/./_app/chunks/vendor-c14e11e8.js"], styles: null}, ".svelte/build/components/error.svelte": {entry: "/./_app/error.svelte-d9f6236e.js", css: [], js: ["/./_app/error.svelte-d9f6236e.js", "/./_app/chunks/vendor-c14e11e8.js"], styles: null}, "src/routes/index.svelte": {entry: "/./_app/pages\\index.svelte-9165fde6.js", css: [], js: ["/./_app/pages\\index.svelte-9165fde6.js", "/./_app/chunks/vendor-c14e11e8.js", "/./_app/chunks/Project-42886bb8.js"], styles: null}, "src/routes/projects/randominator.svelte": {entry: "/./_app/pages\\projects\\randominator.svelte-24317c47.js", css: ["/./_app/assets/Text-b80b2453.css"], js: ["/./_app/pages\\projects\\randominator.svelte-24317c47.js", "/./_app/chunks/vendor-c14e11e8.js", "/./_app/chunks/Text-3219dccd.js"], styles: null}, "src/routes/about.svelte": {entry: "/./_app/pages\\about.svelte-73a65951.js", css: ["/./_app/assets/pages\\about.svelte-7cbe5c12.css"], js: ["/./_app/pages\\about.svelte-73a65951.js", "/./_app/chunks/vendor-c14e11e8.js"], styles: null}, "src/routes/music/autumn.svelte": {entry: "/./_app/pages\\music\\autumn.svelte-4b3d4d89.js", css: ["/./_app/assets/Text-b80b2453.css"], js: ["/./_app/pages\\music\\autumn.svelte-4b3d4d89.js", "/./_app/chunks/vendor-c14e11e8.js", "/./_app/chunks/Text-3219dccd.js"], styles: null}, "src/routes/music.svelte": {entry: "/./_app/pages\\music.svelte-8f1a3e3e.js", css: [], js: ["/./_app/pages\\music.svelte-8f1a3e3e.js", "/./_app/chunks/vendor-c14e11e8.js", "/./_app/chunks/Project-42886bb8.js"], styles: null}};
async function load_component(file) {
  if (!module_lookup[file]) {
    console.log({file});
  }
  return {
    module: await module_lookup[file](),
    ...metadata_lookup[file]
  };
}
function render(request, {
  paths = {base: "", assets: "/."},
  local = false,
  dependencies,
  only_render_prerenderable_pages = false,
  get_static_file
} = {}) {
  return ssr({
    ...request,
    host: request.headers["host"]
  }, {
    paths,
    local,
    template,
    manifest,
    load_component,
    target: "#svelte",
    entry: "/./_app/start-5a99650c.js",
    root: Root,
    hooks,
    dev: false,
    amp: false,
    dependencies,
    only_render_prerenderable_pages,
    get_component_path: (id) => "/./_app/" + entry_lookup[id],
    get_stack: (error2) => error2.stack,
    get_static_file,
    ssr: true,
    router: true,
    hydrate: true
  });
}
var global = "/*! tailwindcss v2.1.1 | MIT License | https://tailwindcss.com*/\n\n/*! modern-normalize v1.0.0 | MIT License | https://github.com/sindresorhus/modern-normalize */:root{-moz-tab-size:4;-o-tab-size:4;tab-size:4}html{line-height:1.15;-webkit-text-size-adjust:100%}body{margin:0;font-family:system-ui,-apple-system,Segoe UI,Roboto,Helvetica,Arial,sans-serif,Apple Color Emoji,Segoe UI Emoji}hr{height:0;color:inherit}abbr[title]{-webkit-text-decoration:underline dotted;text-decoration:underline dotted}b,strong{font-weight:bolder}code,kbd,pre,samp{font-family:ui-monospace,SFMono-Regular,Consolas,Liberation Mono,Menlo,monospace;font-size:1em}small{font-size:80%}sub,sup{font-size:75%;line-height:0;position:relative;vertical-align:baseline}sub{bottom:-.25em}sup{top:-.5em}table{text-indent:0;border-color:inherit}button,input,optgroup,select,textarea{font-family:inherit;font-size:100%;line-height:1.15;margin:0}button,select{text-transform:none}button{-webkit-appearance:button}legend{padding:0}progress{vertical-align:baseline}summary{display:list-item}blockquote,dd,dl,figure,h1,h2,h3,h4,h5,h6,hr,p,pre{margin:0}button{background-color:transparent;background-image:none}button:focus{outline:1px dotted;outline:5px auto -webkit-focus-ring-color}fieldset,ol,ul{margin:0;padding:0}ol,ul{list-style:none}html{font-family:ui-sans-serif,system-ui,-apple-system,BlinkMacSystemFont,Segoe UI,Roboto,Helvetica Neue,Arial,Noto Sans,sans-serif,Apple Color Emoji,Segoe UI Emoji,Segoe UI Symbol,Noto Color Emoji;line-height:1.5}body{font-family:inherit;line-height:inherit}*,:after,:before{box-sizing:border-box;border:0 solid #e5e5e5}hr{border-top-width:1px}img{border-style:solid}textarea{resize:vertical}input::-moz-placeholder, textarea::-moz-placeholder{opacity:1;color:#a3a3a3}input:-ms-input-placeholder, textarea:-ms-input-placeholder{opacity:1;color:#a3a3a3}input::placeholder,textarea::placeholder{opacity:1;color:#a3a3a3}button{cursor:pointer}table{border-collapse:collapse}h1,h2,h3,h4,h5,h6{font-size:inherit;font-weight:inherit}a{color:inherit;text-decoration:inherit}button,input,optgroup,select,textarea{padding:0;line-height:inherit;color:inherit}code,kbd,pre,samp{font-family:ui-monospace,SFMono-Regular,Menlo,Monaco,Consolas,Liberation Mono,Courier New,monospace}audio,canvas,embed,iframe,img,object,svg,video{display:block;vertical-align:middle}img,video{max-width:100%;height:auto}.space-y-2>:not([hidden])~:not([hidden]){--tw-space-y-reverse:0;margin-top:calc(0.5rem*(1 - var(--tw-space-y-reverse)));margin-bottom:calc(0.5rem*var(--tw-space-y-reverse))}.space-x-4>:not([hidden])~:not([hidden]){--tw-space-x-reverse:0;margin-right:calc(1rem*var(--tw-space-x-reverse));margin-left:calc(1rem*(1 - var(--tw-space-x-reverse)))}.bg-gray-200{--tw-bg-opacity:1;background-color:rgba(229,229,229,var(--tw-bg-opacity))}.bg-gray-300{--tw-bg-opacity:1;background-color:rgba(212,212,212,var(--tw-bg-opacity))}.bg-red-500{--tw-bg-opacity:1;background-color:rgba(239,68,68,var(--tw-bg-opacity))}.bg-blue-500{--tw-bg-opacity:1;background-color:rgba(14,165,233,var(--tw-bg-opacity))}.bg-green-200{--tw-bg-opacity:1;background-color:rgba(167,243,208,var(--tw-bg-opacity))}.bg-green-300{--tw-bg-opacity:1;background-color:rgba(110,231,183,var(--tw-bg-opacity))}.hover\\:bg-blue-700:hover{--tw-bg-opacity:1;background-color:rgba(3,105,161,var(--tw-bg-opacity))}@media (prefers-color-scheme:dark){.dark\\:bg-gray-600{--tw-bg-opacity:1;background-color:rgba(82,82,82,var(--tw-bg-opacity))}.dark\\:bg-gray-700{--tw-bg-opacity:1;background-color:rgba(64,64,64,var(--tw-bg-opacity))}.dark\\:bg-gray-800{--tw-bg-opacity:1;background-color:rgba(38,38,38,var(--tw-bg-opacity))}.dark\\:bg-green-500{--tw-bg-opacity:1;background-color:rgba(16,185,129,var(--tw-bg-opacity))}}.border-gray-300{--tw-border-opacity:1;border-color:rgba(212,212,212,var(--tw-border-opacity))}.border-gray-400{--tw-border-opacity:1;border-color:rgba(163,163,163,var(--tw-border-opacity))}.border-green-300{--tw-border-opacity:1;border-color:rgba(110,231,183,var(--tw-border-opacity))}.border-green-400{--tw-border-opacity:1;border-color:rgba(52,211,153,var(--tw-border-opacity))}@media (prefers-color-scheme:dark){.dark\\:border-gray-700{--tw-border-opacity:1;border-color:rgba(64,64,64,var(--tw-border-opacity))}.dark\\:border-green-600{--tw-border-opacity:1;border-color:rgba(5,150,105,var(--tw-border-opacity))}}.rounded{border-radius:.25rem}.rounded-xl{border-radius:.75rem}.rounded-2xl{border-radius:1rem}.border-2{border-width:2px}.border{border-width:1px}.border-t-2{border-top-width:2px}.flex{display:flex}.table{display:table}.hidden{display:none}.flex-row{flex-direction:row}.flex-col{flex-direction:column}.flex-wrap{flex-wrap:wrap}.items-center{align-items:center}.justify-center{justify-content:center}.justify-between{justify-content:space-between}.font-mono{font-family:ui-monospace,SFMono-Regular,Menlo,Monaco,Consolas,Liberation Mono,Courier New,monospace}.font-bold{font-weight:700}.h-auto{height:auto}.h-full{height:100%}.text-xs{font-size:.75rem;line-height:1rem}.text-sm{font-size:.875rem;line-height:1.25rem}.text-base{font-size:1rem;line-height:1.5rem}.text-lg{font-size:1.125rem}.text-lg,.text-xl{line-height:1.75rem}.text-xl{font-size:1.25rem}.text-3xl{font-size:1.875rem;line-height:2.25rem}.text-4xl{font-size:2.25rem;line-height:2.5rem}.leading-tight{line-height:1.25}.my-1{margin-top:.25rem;margin-bottom:.25rem}.mx-1{margin-left:.25rem;margin-right:.25rem}.mx-4{margin-left:1rem;margin-right:1rem}.my-6{margin-top:1.5rem;margin-bottom:1.5rem}.my-auto{margin-top:auto;margin-bottom:auto}.mx-auto{margin-left:auto;margin-right:auto}.mr-2{margin-right:.5rem}.mb-2{margin-bottom:.5rem}.mb-3{margin-bottom:.75rem}.mb-8{margin-bottom:2rem}.mt-16{margin-top:4rem}.p-4{padding:1rem}.py-1{padding-top:.25rem;padding-bottom:.25rem}.px-1{padding-left:.25rem;padding-right:.25rem}.py-2{padding-top:.5rem;padding-bottom:.5rem}.px-2{padding-left:.5rem;padding-right:.5rem}.py-4{padding-top:1rem;padding-bottom:1rem}.px-4{padding-left:1rem;padding-right:1rem}.py-6{padding-top:1.5rem;padding-bottom:1.5rem}.px-1\\.5{padding-left:.375rem;padding-right:.375rem}.pt-3{padding-top:.75rem}.pt-6{padding-top:1.5rem}.pt-10{padding-top:2.5rem}.pb-10{padding-bottom:2.5rem}*{--tw-shadow:0 0 transparent}.shadow-md{--tw-shadow:0 4px 6px -1px rgba(0,0,0,0.1),0 2px 4px -1px rgba(0,0,0,0.06)}.hover\\:shadow-xl:hover,.shadow-md{box-shadow:var(--tw-ring-offset-shadow,0 0 transparent),var(--tw-ring-shadow,0 0 transparent),var(--tw-shadow)}.hover\\:shadow-xl:hover{--tw-shadow:0 20px 25px -5px rgba(0,0,0,0.1),0 10px 10px -5px rgba(0,0,0,0.04)}*{--tw-ring-inset:var(--tw-empty,/*!*/ /*!*/);--tw-ring-offset-width:0px;--tw-ring-offset-color:#fff;--tw-ring-color:rgba(14,165,233,0.5);--tw-ring-offset-shadow:0 0 transparent;--tw-ring-shadow:0 0 transparent}.text-left{text-align:left}.text-center{text-align:center}.text-gray-500{--tw-text-opacity:1;color:rgba(115,115,115,var(--tw-text-opacity))}.text-gray-700{--tw-text-opacity:1;color:rgba(64,64,64,var(--tw-text-opacity))}.text-gray-900{--tw-text-opacity:1;color:rgba(23,23,23,var(--tw-text-opacity))}.text-green-500{--tw-text-opacity:1;color:rgba(16,185,129,var(--tw-text-opacity))}.text-white{--tw-text-opacity:1;color:rgba(255,255,255,var(--tw-text-opacity))}@media (prefers-color-scheme:dark){.dark\\:text-gray-200{--tw-text-opacity:1;color:rgba(229,229,229,var(--tw-text-opacity))}.dark\\:text-gray-300{--tw-text-opacity:1;color:rgba(212,212,212,var(--tw-text-opacity))}.dark\\:text-gray-400{--tw-text-opacity:1;color:rgba(163,163,163,var(--tw-text-opacity))}}.hover\\:underline:hover,.underline{text-decoration:underline}.tracking-wider{letter-spacing:.05em}.w-auto{width:auto}.w-10\\/12{width:83.333333%}.w-11\\/12{width:91.666667%}.w-full{width:100%}.transform{--tw-translate-x:0;--tw-translate-y:0;--tw-rotate:0;--tw-skew-x:0;--tw-skew-y:0;--tw-scale-x:1;--tw-scale-y:1;transform:translateX(var(--tw-translate-x)) translateY(var(--tw-translate-y)) rotate(var(--tw-rotate)) skewX(var(--tw-skew-x)) skewY(var(--tw-skew-y)) scaleX(var(--tw-scale-x)) scaleY(var(--tw-scale-y))}.hover\\:scale-101:hover{--tw-scale-x:1.01;--tw-scale-y:1.01}.hover\\:-translate-y-1:hover{--tw-translate-y:-0.25rem}.transition{transition-property:background-color,border-color,color,fill,stroke,opacity,box-shadow,transform,filter,-webkit-backdrop-filter;transition-property:background-color,border-color,color,fill,stroke,opacity,box-shadow,transform,filter,backdrop-filter;transition-property:background-color,border-color,color,fill,stroke,opacity,box-shadow,transform,filter,backdrop-filter,-webkit-backdrop-filter;transition-timing-function:cubic-bezier(.4,0,.2,1);transition-duration:.15s}@-webkit-keyframes spin{to{transform:rotate(1turn)}}@keyframes spin{to{transform:rotate(1turn)}}@-webkit-keyframes ping{75%,to{transform:scale(2);opacity:0}}@keyframes ping{75%,to{transform:scale(2);opacity:0}}@-webkit-keyframes pulse{50%{opacity:.5}}@keyframes pulse{50%{opacity:.5}}@-webkit-keyframes bounce{0%,to{transform:translateY(-25%);-webkit-animation-timing-function:cubic-bezier(.8,0,1,1);animation-timing-function:cubic-bezier(.8,0,1,1)}50%{transform:none;-webkit-animation-timing-function:cubic-bezier(0,0,.2,1);animation-timing-function:cubic-bezier(0,0,.2,1)}}@keyframes bounce{0%,to{transform:translateY(-25%);-webkit-animation-timing-function:cubic-bezier(.8,0,1,1);animation-timing-function:cubic-bezier(.8,0,1,1)}50%{transform:none;-webkit-animation-timing-function:cubic-bezier(0,0,.2,1);animation-timing-function:cubic-bezier(0,0,.2,1)}}.filter{--tw-blur:var(--tw-empty,/*!*/ /*!*/);--tw-brightness:var(--tw-empty,/*!*/ /*!*/);--tw-contrast:var(--tw-empty,/*!*/ /*!*/);--tw-grayscale:var(--tw-empty,/*!*/ /*!*/);--tw-hue-rotate:var(--tw-empty,/*!*/ /*!*/);--tw-invert:var(--tw-empty,/*!*/ /*!*/);--tw-saturate:var(--tw-empty,/*!*/ /*!*/);--tw-sepia:var(--tw-empty,/*!*/ /*!*/);--tw-drop-shadow:var(--tw-empty,/*!*/ /*!*/);filter:var(--tw-blur) var(--tw-brightness) var(--tw-contrast) var(--tw-grayscale) var(--tw-hue-rotate) var(--tw-invert) var(--tw-saturate) var(--tw-sepia) var(--tw-drop-shadow)}.drop-shadow{--tw-drop-shadow:drop-shadow(0 1px 2px rgba(0,0,0,0.1)) drop-shadow(0 1px 1px rgba(0,0,0,0.06))}@media (min-width:640px){.sm\\:w-2\\/3{width:66.666667%}}@media (min-width:768px){.md\\:flex{display:flex}.md\\:flex-row{flex-direction:row}.md\\:flex-wrap{flex-wrap:wrap}.md\\:items-end{align-items:flex-end}.md\\:justify-between{justify-content:space-between}.md\\:justify-evenly{justify-content:space-evenly}.md\\:h-48{height:12rem}.md\\:text-sm{font-size:.875rem;line-height:1.25rem}.md\\:text-base{font-size:1rem;line-height:1.5rem}.md\\:text-lg{font-size:1.125rem;line-height:1.75rem}.md\\:text-xl{font-size:1.25rem;line-height:1.75rem}.md\\:text-2xl{font-size:1.5rem;line-height:2rem}.md\\:text-5xl{font-size:3rem;line-height:1}.md\\:my-1{margin-top:.25rem;margin-bottom:.25rem}.md\\:mx-1{margin-left:.25rem;margin-right:.25rem}.md\\:mx-4{margin-left:1rem;margin-right:1rem}.md\\:mx-14{margin-left:3.5rem;margin-right:3.5rem}.md\\:my-1\\.5{margin-top:.375rem;margin-bottom:.375rem}.md\\:mx-1\\.5{margin-left:.375rem;margin-right:.375rem}.md\\:mb-6{margin-bottom:1.5rem}.md\\:py-1{padding-top:.25rem;padding-bottom:.25rem}.md\\:px-2{padding-left:.5rem;padding-right:.5rem}.md\\:py-1\\.5{padding-top:.375rem;padding-bottom:.375rem}.md\\:text-justify{text-align:justify}.md\\:w-96{width:24rem}.md\\:w-auto{width:auto}.md\\:w-8\\/12{width:66.666667%}.md\\:w-full{width:100%}}@media (min-width:1024px){.lg\\:text-4xl{font-size:2.25rem;line-height:2.5rem}.lg\\:tracking-wider{letter-spacing:.05em}}@media (min-width:1280px){.xl\\:mx-40{margin-left:10rem;margin-right:10rem}}";
var $layout_svelte_svelte_type_style_lang = ".selected.svelte-ltbjvj{filter:drop-shadow(0 0 3px rgba(16,185,129,.4));font-weight:700;--tw-text-opacity:1;color:rgba(16,185,129,var(--tw-text-opacity));text-decoration:underline}";
const css$2 = {
  code: ".selected.svelte-ltbjvj{filter:drop-shadow(0 0 3px rgba(16,185,129,.4));font-weight:700;--tw-text-opacity:1;color:rgba(16,185,129,var(--tw-text-opacity));text-decoration:underline}",
  map: `{"version":3,"file":"$layout.svelte","sources":["$layout.svelte"],"sourcesContent":["<script>\\n\\timport '../global.css';\\n\\n\\t/**\\n\\t * 1 = About\\n\\t * 2 = Projects\\n\\t * 3 = Music\\n\\t */\\n\\tlet selected = 2;\\n</script>\\n\\n<svelte:head>\\n\\t<title>Tilen's creations</title>\\n</svelte:head>\\n\\n<main class=\\"font-mono mx-4 md:mx-14 lg:mx-30 xl:mx-40\\">\\n\\t<!-- HEADER -->\\n\\t<div\\n\\t\\tclass=\\"dark:text-gray-200 text-gray-900 md:items-end flex flex-row justify-center md:justify-between pt-10 mb-8\\"\\n\\t>\\n\\t\\t<!-- LEFT SIDE -->\\n\\t\\t<a\\n\\t\\t\\thref=\\"../about\\"\\n\\t\\t\\tclass=\\"hidden md:flex text-3xl lg:text-4xl lg:tracking-wider\\"\\n\\t\\t\\ton:click={() => (selected = 1)}>Tilen's Creations</a\\n\\t\\t>\\n\\n\\t\\t<!-- RIGHT SIDE -->\\n\\t\\t<p class=\\"flex space-x-4 text-xl md:text-2xl w-10/12 md:w-auto justify-between\\">\\n\\t\\t\\t<a\\n\\t\\t\\t\\thref=\\"../about\\"\\n\\t\\t\\t\\tclass=\\"hover:underline\\"\\n\\t\\t\\t\\tclass:selected={selected === 1}\\n\\t\\t\\t\\ton:click={() => (selected = 1)}>About</a\\n\\t\\t\\t>\\n\\t\\t\\t<a\\n\\t\\t\\t\\thref=\\"../\\"\\n\\t\\t\\t\\tclass=\\"hover:underline selected-section\\"\\n\\t\\t\\t\\tclass:selected={selected === 2}\\n\\t\\t\\t\\ton:click={() => (selected = 2)}>Projects</a\\n\\t\\t\\t>\\n\\t\\t\\t<a\\n\\t\\t\\t\\thref=\\"../music\\"\\n\\t\\t\\t\\tclass=\\"hover:underline\\"\\n\\t\\t\\t\\tclass:selected={selected === 3}\\n\\t\\t\\t\\ton:click={() => (selected = 3)}>Music</a\\n\\t\\t\\t>\\n\\t\\t</p>\\n\\t</div>\\n\\n\\t<!-- CONTENT -->\\n\\t<div class=\\"pb-10\\">\\n\\t\\t<slot />\\n\\t</div>\\n\\n\\t<!-- FOOTER -->\\n\\t<div class=\\"mx-auto w-10/12 md:w-full\\">\\n\\t\\t<div class=\\"mt-16 border-t-2 border-gray-300 dark:border-gray-700 flex flex-col items-center\\">\\n\\t\\t\\t<div class=\\"sm:w-2/3 text-center py-6\\">\\n\\t\\t\\t\\t<p class=\\"text-sm text-green-500 font-bold mb-2\\">\xA9 2021 by Tilen Lampret</p>\\n\\t\\t\\t</div>\\n\\t\\t</div>\\n\\t</div>\\n</main>\\n\\n<style>.selected{filter:drop-shadow(0 0 3px rgba(16,185,129,.4));font-weight:700;--tw-text-opacity:1;color:rgba(16,185,129,var(--tw-text-opacity));text-decoration:underline}.text-shadow{text-shadow:0 4px 10px rgba(0,0,0,.19)}</style>\\n"],"names":[],"mappings":"AAiEO,uBAAS,CAAC,OAAO,YAAY,CAAC,CAAC,CAAC,CAAC,GAAG,CAAC,KAAK,EAAE,CAAC,GAAG,CAAC,GAAG,CAAC,EAAE,CAAC,CAAC,CAAC,YAAY,GAAG,CAAC,kBAAkB,CAAC,CAAC,MAAM,KAAK,EAAE,CAAC,GAAG,CAAC,GAAG,CAAC,IAAI,iBAAiB,CAAC,CAAC,CAAC,gBAAgB,SAAS,CAAC"}`
};
const $layout = create_ssr_component(($$result, $$props, $$bindings, slots) => {
  $$result.css.add(css$2);
  return `${$$result.head += `${$$result.title = `<title>Tilen&#39;s creations</title>`, ""}`, ""}

<main class="${"font-mono mx-4 md:mx-14 lg:mx-30 xl:mx-40"}">
	<div class="${"dark:text-gray-200 text-gray-900 md:items-end flex flex-row justify-center md:justify-between pt-10 mb-8"}">
		<a href="${"../about"}" class="${"hidden md:flex text-3xl lg:text-4xl lg:tracking-wider"}">Tilen&#39;s Creations</a>

		
		<p class="${"flex space-x-4 text-xl md:text-2xl w-10/12 md:w-auto justify-between"}"><a href="${"../about"}" class="${["hover:underline svelte-ltbjvj", ""].join(" ").trim()}">About</a>
			<a href="${"../"}" class="${[
    "hover:underline selected-section svelte-ltbjvj",
    "selected"
  ].join(" ").trim()}">Projects</a>
			<a href="${"../music"}" class="${["hover:underline svelte-ltbjvj", ""].join(" ").trim()}">Music</a></p></div>

	
	<div class="${"pb-10"}">${slots.default ? slots.default({}) : ``}</div>

	
	<div class="${"mx-auto w-10/12 md:w-full"}"><div class="${"mt-16 border-t-2 border-gray-300 dark:border-gray-700 flex flex-col items-center"}"><div class="${"sm:w-2/3 text-center py-6"}"><p class="${"text-sm text-green-500 font-bold mb-2"}">\xA9 2021 by Tilen Lampret</p></div></div></div>
</main>`;
});
var $layout$1 = /* @__PURE__ */ Object.freeze({
  __proto__: null,
  [Symbol.toStringTag]: "Module",
  default: $layout
});
function load({error: error2, status}) {
  return {props: {error: error2, status}};
}
const Error$1 = create_ssr_component(($$result, $$props, $$bindings, slots) => {
  let {status} = $$props;
  let {error: error2} = $$props;
  if ($$props.status === void 0 && $$bindings.status && status !== void 0)
    $$bindings.status(status);
  if ($$props.error === void 0 && $$bindings.error && error2 !== void 0)
    $$bindings.error(error2);
  return `<h1>${escape(status)}</h1>

<p>${escape(error2.message)}</p>


${error2.stack ? `<pre>${escape(error2.stack)}</pre>` : ``}`;
});
var error = /* @__PURE__ */ Object.freeze({
  __proto__: null,
  [Symbol.toStringTag]: "Module",
  default: Error$1,
  load
});
const Project = create_ssr_component(($$result, $$props, $$bindings, slots) => {
  let {name = "Name was not given!"} = $$props;
  let {description = "Description not given!"} = $$props;
  let {tags = ["test", "\u{1F916}"]} = $$props;
  let {href = "Href not given!"} = $$props;
  let {year = 1990} = $$props;
  if ($$props.name === void 0 && $$bindings.name && name !== void 0)
    $$bindings.name(name);
  if ($$props.description === void 0 && $$bindings.description && description !== void 0)
    $$bindings.description(description);
  if ($$props.tags === void 0 && $$bindings.tags && tags !== void 0)
    $$bindings.tags(tags);
  if ($$props.href === void 0 && $$bindings.href && href !== void 0)
    $$bindings.href(href);
  if ($$props.year === void 0 && $$bindings.year && year !== void 0)
    $$bindings.year(year);
  return `<div class="${"font-mono bg-gray-200 border-gray-400 dark:bg-gray-600 dark:border-gray-700 md:h-48 w-10/12 md:w-96 rounded-2xl shadow-md transition hover:shadow-xl transform hover:scale-101 hover:-translate-y-1 border-2"}"><div class="${"flex h-full"}">
		<div class="${"flex flex-col justify-between p-4 text-left font-mono w-full space-y-2"}">
			<a href="${"./" + escape(href)}" class="${"dark:text-gray-200 font-bold text-xl md:text-2xl leading-tight text-black hover:underline tracking-wider"}">${escape(name)}</a>

			
			<p class="${"dark:text-gray-300 text-gray-500 text-sm md:text-base"}">${escape(description)}</p>

			
			<div class="${"flex justify-between w-full text-xs md:text-sm"}">
				<div class="${"flex"}">${each(tags, (tag) => `<div class="${"dark:bg-gray-700 dark:border-gray-700 dark:text-gray-200 py-1 px-2 mr-2 bg-gray-300 rounded-xl border border-gray-400"}">${escape(tag)}</div>`)}</div>
				
				<div class="${"my-auto rounded-xl py-1 px-2 bg-green-300 border border-green-400 dark:bg-green-500 dark:border-green-600"}">${escape(year)}</div></div></div></div></div>`;
});
const Routes = create_ssr_component(($$result, $$props, $$bindings, slots) => {
  const projects = [
    {
      name: "Randominator",
      description: "A simple program, that generates random ideas",
      href: "projects/randominator",
      tags: ["\u{1F4A1} Ideas", "\u{1F3B2} RNG"],
      year: 2020
    }
  ];
  return `<div class="${"flex justify-center flex-col md:flex-row md:flex-wrap md:justify-evenly"}">${each(projects, (proj) => `<div class="${"flex justify-center my-6 md:mx-4 md:mb-6"}">${validate_component(Project, "Project").$$render($$result, Object.assign(proj), {}, {})}
    </div>`)}</div>`;
});
var index = /* @__PURE__ */ Object.freeze({
  __proto__: null,
  [Symbol.toStringTag]: "Module",
  default: Routes
});
var Text_svelte_svelte_type_style_lang = "div.svelte-1hyqcws h1{font-weight:700;font-size:1.25rem;line-height:1.75rem}@media(min-width:768px){div.svelte-1hyqcws h1{font-size:1.5rem;line-height:2rem}}@media(min-width:768px){div.svelte-1hyqcws p{font-size:1.125rem;line-height:1.75rem;text-align:justify}}div.svelte-1hyqcws h2{font-weight:800;font-size:1.125rem;line-height:1.75rem}@media(min-width:768px){div.svelte-1hyqcws h2{font-size:1.25rem;line-height:1.75rem}}div.svelte-1hyqcws a{font-weight:700;--tw-text-opacity:1;color:rgba(16,185,129,var(--tw-text-opacity));text-decoration:underline}";
const css$1 = {
  code: "div.svelte-1hyqcws h1{font-weight:700;font-size:1.25rem;line-height:1.75rem}@media(min-width:768px){div.svelte-1hyqcws h1{font-size:1.5rem;line-height:2rem}}@media(min-width:768px){div.svelte-1hyqcws p{font-size:1.125rem;line-height:1.75rem;text-align:justify}}div.svelte-1hyqcws h2{font-weight:800;font-size:1.125rem;line-height:1.75rem}@media(min-width:768px){div.svelte-1hyqcws h2{font-size:1.25rem;line-height:1.75rem}}div.svelte-1hyqcws a{font-weight:700;--tw-text-opacity:1;color:rgba(16,185,129,var(--tw-text-opacity));text-decoration:underline}",
  map: '{"version":3,"file":"Text.svelte","sources":["Text.svelte"],"sourcesContent":["\\r\\n<div class=\\"w-11/12 lg:8/12 mx-auto pt-6 dark:text-gray-200\\">\\r\\n  <slot />\\r\\n</div>\\r\\n\\r\\n<style>div :global(h1){font-weight:700;font-size:1.25rem;line-height:1.75rem}@media (min-width:768px){div :global(h1){font-size:1.5rem;line-height:2rem}}@media (min-width:768px){div :global(p){font-size:1.125rem;line-height:1.75rem;text-align:justify}}div :global(h2){font-weight:800;font-size:1.125rem;line-height:1.75rem}@media (min-width:768px){div :global(h2){font-size:1.25rem;line-height:1.75rem}}div :global(a){font-weight:700;--tw-text-opacity:1;color:rgba(16,185,129,var(--tw-text-opacity));text-decoration:underline}</style>"],"names":[],"mappings":"AAKO,kBAAG,CAAC,AAAQ,EAAE,AAAC,CAAC,YAAY,GAAG,CAAC,UAAU,OAAO,CAAC,YAAY,OAAO,CAAC,MAAM,AAAC,WAAW,KAAK,CAAC,CAAC,kBAAG,CAAC,AAAQ,EAAE,AAAC,CAAC,UAAU,MAAM,CAAC,YAAY,IAAI,CAAC,CAAC,MAAM,AAAC,WAAW,KAAK,CAAC,CAAC,kBAAG,CAAC,AAAQ,CAAC,AAAC,CAAC,UAAU,QAAQ,CAAC,YAAY,OAAO,CAAC,WAAW,OAAO,CAAC,CAAC,kBAAG,CAAC,AAAQ,EAAE,AAAC,CAAC,YAAY,GAAG,CAAC,UAAU,QAAQ,CAAC,YAAY,OAAO,CAAC,MAAM,AAAC,WAAW,KAAK,CAAC,CAAC,kBAAG,CAAC,AAAQ,EAAE,AAAC,CAAC,UAAU,OAAO,CAAC,YAAY,OAAO,CAAC,CAAC,kBAAG,CAAC,AAAQ,CAAC,AAAC,CAAC,YAAY,GAAG,CAAC,kBAAkB,CAAC,CAAC,MAAM,KAAK,EAAE,CAAC,GAAG,CAAC,GAAG,CAAC,IAAI,iBAAiB,CAAC,CAAC,CAAC,gBAAgB,SAAS,CAAC"}'
};
const Text = create_ssr_component(($$result, $$props, $$bindings, slots) => {
  $$result.css.add(css$1);
  return `<div class="${"w-11/12 lg:8/12 mx-auto pt-6 dark:text-gray-200 svelte-1hyqcws"}">${slots.default ? slots.default({}) : ``}
</div>`;
});
const Randominator = create_ssr_component(($$result, $$props, $$bindings, slots) => {
  return `${validate_component(Text, "Text").$$render($$result, {}, {}, {
    default: () => `<h1>\u{1F4A1} Randominator</h1>
  <br>
  <p>You can download the code from <a href="${"https://github.com/tilenl/Randominator"}">github</a>.
  </p>
  <br>

  <h2>Why the name?</h2>
  <p>I watched a lot of <a href="${"https://www.youtube.com/watch?v=NkQrKxTFARM"}">Phineas and Ferb</a> when I was in primary school, and I still remember <a href="${"https://milomurphyslaw.fandom.com/wiki/List_of_Inators_and_inventions_by_Heinz_Doofenshmirtz"}">Doofenshmirtz&#39;s inventions</a>. Anything he created, he somehow managed to name &quot;insert anything&quot;-inator. Because of the stylish names he gave his inventions, I didn not want to stride far away with my project name, so I called it the <b>Randominator</b>!
  </p>
  <br>

  <h2>How...</h2>
  <p>It started as an idea to generate random game ideas, but I wanted it to be more generic. The major pain point originated from my game development path, where I wanted to practise making games, but I didn&#39;t have any ideas for short and quirky games.
  </p>

  <br>
  <h2>Before V2</h2>
  <p>The first version of the randominator was nothing more than a copy of <a href="${"https://orteil.dashnet.org/gamegen"}">Orteil&#39;s website generator</a>. It generated some good ideas, but the data was hardcoded into the program itself, which was a problem if I wanted to add new entries. Besides the data problem I also wanted to be able to give the program a template, how the generated sentences should look.
  </p>

  <br>
  <h2>Into the future-&gt;</h2>
  <p>There is still <b>a lot</b> I can improve. I am going to rewrite the whole program in Rust language, as I do think it will help with the general bug catching, but until then, I hope that some will find the program useful (also much easier to download the code through the use of cargo).
  </p>`
  })}`;
});
var randominator = /* @__PURE__ */ Object.freeze({
  __proto__: null,
  [Symbol.toStringTag]: "Module",
  default: Randominator
});
var about_svelte_svelte_type_style_lang = ".text-shadow.svelte-qi4o4y{text-shadow:0 4px 10px rgba(0,0,0,.3)}";
const css = {
  code: ".text-shadow.svelte-qi4o4y{text-shadow:0 4px 10px rgba(0,0,0,.3)}",
  map: `{"version":3,"file":"about.svelte","sources":["about.svelte"],"sourcesContent":["<script>\\r\\n\\tconst loves = [\\r\\n\\t\\t'\u{1F453} c#',\\r\\n\\t\\t'\u{1F980} Rust',\\r\\n\\t\\t'\u{1F451} Nim',\\r\\n\\t\\t'\u{1F393} C',\\r\\n\\t\\t'\u{1F578} Web dev',\\r\\n\\t\\t'\u{1F3A8} Figma',\\r\\n\\t\\t'\u{1F3AE} Unity',\\r\\n\\t\\t'\u{1F369} Blender',\\r\\n\\t\\t'\u{1F916} Godot',\\r\\n\\t\\t'\u{1F30C} Shaders',\\r\\n\\t\\t'\u{1F4BB} OpenGL',\\r\\n\\t\\t'\u2615 Java',\\r\\n\\t\\t'\u{1F3B5} Music',\\r\\n\\t\\t'\u{1F375} Tea'\\r\\n\\t];\\r\\n</script>\\r\\n\\r\\n<div class=\\"w-10/12 md:w-8/12 mx-auto\\">\\r\\n\\t<!-- Hi! -->\\r\\n\\t<h1 class=\\"dark:text-gray-200 text-shadow font-bold text-4xl md:text-5xl pt-6 tracking-wider\\">Hi \u{1F44B}!</h1>\\r\\n\\t<h2 class=\\"text-gray-700 dark:text-gray-400 text-base md:text-lg pt-3\\">I'm Tilen, also known as Jeff</h2>\\r\\n\\r\\n\\t<br />\\r\\n\\r\\n\\t<div class=\\"text-base md:text-lg dark:text-gray-200\\">\\r\\n\\t\\t<!-- Student and Bassist -->\\r\\n\\t\\t<div>\\r\\n\\t\\t\\t<p>\\r\\n\\t\\t\\t\\t- Student at <a\\r\\n\\t\\t\\t\\t\\thref=\\"https://www.fri.uni-lj.si/en\\"\\r\\n\\t\\t\\t\\t\\tclass=\\"underline text-green-500 font-bold\\">FRI</a\\r\\n\\t\\t\\t\\t>\\r\\n\\t\\t\\t</p>\\r\\n\\t\\t\\t<p>\\r\\n\\t\\t\\t\\t- Bassist at <a href=\\"https://www.ryvertone.com/\\" class=\\"underline text-green-500 font-bold\\"\\r\\n\\t\\t\\t\\t\\t>Ryvertone</a\\r\\n\\t\\t\\t\\t>\\r\\n\\t\\t\\t</p>\\r\\n\\t\\t</div>\\r\\n    <br />\\r\\n\\t\\t<!-- Support me -->\\r\\n\\t\\t<div>\\r\\n\\t\\t\\t<h3>\\r\\n\\t\\t\\t\\t - Support me on <a class=\\"underline text-green-500 font-bold\\" href=\\"https://ko-fi.com/tilenl\\"\\r\\n\\t\\t\\t\\t\\t>Ko-Fi</a\\r\\n\\t\\t\\t\\t>\\r\\n\\t\\t\\t</h3>\\r\\n\\t\\t\\t<h3>\\r\\n\\t\\t\\t\\t - Visit my <a class=\\"underline text-green-500 font-bold\\" href=\\"https://github.com/tilenl\\"\\r\\n\\t\\t\\t\\t\\t>Github</a\\r\\n\\t\\t\\t\\t> page\\r\\n\\t\\t\\t</h3>\\r\\n\\t\\t</div>\\r\\n\\t</div>\\r\\n\\r\\n\\t<br />\\r\\n\\r\\n\\t<h2 class=\\"text-xl md:text-2xl mb-3 dark:text-gray-200\\">Things I love</h2>\\r\\n\\t<div class=\\"flex flex-row flex-wrap\\">\\r\\n\\t\\t{#each loves as love}\\r\\n\\t\\t\\t<p\\r\\n\\t\\t\\t\\tclass=\\"text-sm md:text-base w-auto py-1 md:py-1.5 px-1.5 md:px-2 h-auto bg-green-200 border-green-300 dark:bg-green-500 dark:border-green-600 border-2 rounded-xl mx-1 my-1 md:mx-1.5 md:my-1.5\\"\\r\\n\\t\\t\\t>\\r\\n\\t\\t\\t\\t{love}\\r\\n\\t\\t\\t</p>\\r\\n\\t\\t{/each}\\r\\n\\t</div>\\r\\n</div>\\r\\n\\r\\n<style>.text-shadow{text-shadow:0 4px 10px rgba(0,0,0,.3)}</style>\\r\\n"],"names":[],"mappings":"AAuEO,0BAAY,CAAC,YAAY,CAAC,CAAC,GAAG,CAAC,IAAI,CAAC,KAAK,CAAC,CAAC,CAAC,CAAC,CAAC,CAAC,EAAE,CAAC,CAAC"}`
};
const About = create_ssr_component(($$result, $$props, $$bindings, slots) => {
  const loves = [
    "\u{1F453} c#",
    "\u{1F980} Rust",
    "\u{1F451} Nim",
    "\u{1F393} C",
    "\u{1F578} Web dev",
    "\u{1F3A8} Figma",
    "\u{1F3AE} Unity",
    "\u{1F369} Blender",
    "\u{1F916} Godot",
    "\u{1F30C} Shaders",
    "\u{1F4BB} OpenGL",
    "\u2615 Java",
    "\u{1F3B5} Music",
    "\u{1F375} Tea"
  ];
  $$result.css.add(css);
  return `<div class="${"w-10/12 md:w-8/12 mx-auto"}">
	<h1 class="${"dark:text-gray-200 text-shadow font-bold text-4xl md:text-5xl pt-6 tracking-wider svelte-qi4o4y"}">Hi \u{1F44B}!</h1>
	<h2 class="${"text-gray-700 dark:text-gray-400 text-base md:text-lg pt-3"}">I&#39;m Tilen, also known as Jeff</h2>

	<br>

	<div class="${"text-base md:text-lg dark:text-gray-200"}">
		<div><p>- Student at <a href="${"https://www.fri.uni-lj.si/en"}" class="${"underline text-green-500 font-bold"}">FRI</a></p>
			<p>- Bassist at <a href="${"https://www.ryvertone.com/"}" class="${"underline text-green-500 font-bold"}">Ryvertone</a></p></div>
    <br>
		
		<div><h3>- Support me on <a class="${"underline text-green-500 font-bold"}" href="${"https://ko-fi.com/tilenl"}">Ko-Fi</a></h3>
			<h3>- Visit my <a class="${"underline text-green-500 font-bold"}" href="${"https://github.com/tilenl"}">Github</a> page
			</h3></div></div>

	<br>

	<h2 class="${"text-xl md:text-2xl mb-3 dark:text-gray-200"}">Things I love</h2>
	<div class="${"flex flex-row flex-wrap"}">${each(loves, (love) => `<p class="${"text-sm md:text-base w-auto py-1 md:py-1.5 px-1.5 md:px-2 h-auto bg-green-200 border-green-300 dark:bg-green-500 dark:border-green-600 border-2 rounded-xl mx-1 my-1 md:mx-1.5 md:my-1.5"}">${escape(love)}
			</p>`)}</div>
</div>`;
});
var about = /* @__PURE__ */ Object.freeze({
  __proto__: null,
  [Symbol.toStringTag]: "Module",
  default: About
});
const Autumn = create_ssr_component(($$result, $$props, $$bindings, slots) => {
  return `${validate_component(Text, "Text").$$render($$result, {}, {}, {
    default: () => `<h1>\u{1F341} Autumn</h1>
  <h2>a short piano song</h2>
	<br>
	<p>Original track page is on
		<a href="${"https://www.notion.so/Autumn-ee18878836844a43917393f277cf3e37"}">Notion</a></p>
	<br>
  <h2>Inspiration</h2>
	<p>The idea for the track came in the middle of summer (2020). I was doodling on the piano,
		when it struck me that the melody invokes a feeling similar to the vibes of autumn. I started
		expanding the idea, which grew day by day, until a 4 piece album (is it still called an album?)
		emerged in my mind. It would contain 1 piece for each season: Autumn, Spring, Summer and Winter.
	</p>
  <br>
  <p>The first of four, Autumn, was made around the end of the year 2020.
  </p>

  <br>
  <h2>Song cover</h2>
  <p>I used a little trick, to achieve the wanted cover effect. As I come from a more technical background, I knew of a technique called 
    <a href="${"https://medium.com/tensorflow/neural-style-transfer-creating-art-with-deep-learning-using-tf-keras-and-eager-execution-7d541ac31398"}">Neural Style Transfer</a>, which was perfect for me and my autumn project.
</p>`
  })}`;
});
var autumn = /* @__PURE__ */ Object.freeze({
  __proto__: null,
  [Symbol.toStringTag]: "Module",
  default: Autumn
});
const Music = create_ssr_component(($$result, $$props, $$bindings, slots) => {
  const projects = [
    {
      name: "Autumn",
      description: "A short piano composition on the theme of autumn",
      href: "music/autumn",
      tags: ["\u{1F3B9} Piano", "\u{1F341} Autumn"],
      year: 2020
    }
  ];
  return `<div class="${"flex justify-center flex-col md:flex-row md:flex-wrap md:justify-evenly"}">${each(projects, (proj) => `<div class="${"flex justify-center my-6 md:mx-4 md:mb-6"}">${validate_component(Project, "Project").$$render($$result, Object.assign(proj), {}, {})}
    </div>`)}</div>`;
});
var music = /* @__PURE__ */ Object.freeze({
  __proto__: null,
  [Symbol.toStringTag]: "Module",
  default: Music
});
export {init, render};
