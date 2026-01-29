const http = require("http");
const fs = require("fs");
const path = require("path");
const { spawn } = require("child_process");

const PORT = process.env.PORT || 5173;
const ROOT = __dirname;
const EXE_PATH = path.join(ROOT, "Hegel Infix.exe");
const MAX_NUMBERS = 8;
const DEFAULT_LIMIT = 200;
const MAX_LIMIT = 1000;
const TIMEOUT_MS = 10000;

const MIME = {
  ".html": "text/html; charset=utf-8",
  ".css": "text/css; charset=utf-8",
  ".js": "text/javascript; charset=utf-8",
  ".json": "application/json; charset=utf-8"
};

function sendJson(res, status, data) {
  res.writeHead(status, { "Content-Type": MIME[".json"] });
  res.end(JSON.stringify(data));
}

function parseBody(req) {
  return new Promise((resolve, reject) => {
    let body = "";
    req.on("data", (chunk) => {
      body += chunk;
      if (body.length > 1e6) {
        req.destroy();
        reject(new Error("payload too large"));
      }
    });
    req.on("end", () => {
      try {
        resolve(JSON.parse(body || "{}"));
      } catch (err) {
        reject(err);
      }
    });
  });
}

function tokenize(expr) {
  const tokens = [];
  const isDigit = (c) => /[0-9]/.test(c);
  const isAlpha = (c) => /[a-z]/i.test(c);
  let i = 0;
  while (i < expr.length) {
    const ch = expr[i];
    if (ch === " " || ch === "\t" || ch === "\r" || ch === "\n") {
      i += 1;
      continue;
    }
    if (ch === "(" || ch === ")" || ch === "," || ch === "!" || ch === "+" || ch === "*" || ch === "/") {
      tokens.push({ type: "symbol", value: ch });
      i += 1;
      continue;
    }
    if (ch === "-") {
      const prev = tokens[tokens.length - 1];
      const next = expr[i + 1];
      const unary = !prev || (prev.type === "symbol" && (prev.value === "(" || prev.value === "," || "+-*/".includes(prev.value)));
      if (unary && next && isDigit(next)) {
        let j = i + 1;
        while (j < expr.length && isDigit(expr[j])) j += 1;
        tokens.push({ type: "number", value: expr.slice(i, j) });
        i = j;
        continue;
      }
      tokens.push({ type: "symbol", value: ch });
      i += 1;
      continue;
    }
    if (isDigit(ch)) {
      let j = i + 1;
      while (j < expr.length && isDigit(expr[j])) j += 1;
      tokens.push({ type: "number", value: expr.slice(i, j) });
      i = j;
      continue;
    }
    if (isAlpha(ch)) {
      let j = i + 1;
      while (j < expr.length && isAlpha(expr[j])) j += 1;
      tokens.push({ type: "ident", value: expr.slice(i, j) });
      i = j;
      continue;
    }
    throw new Error(`unexpected char: ${ch}`);
  }
  return tokens;
}

function parseToAst(tokens) {
  let idx = 0;
  const peek = () => tokens[idx];
  const match = (value) => {
    if (tokens[idx] && tokens[idx].value === value) {
      idx += 1;
      return true;
    }
    return false;
  };
  const expect = (value) => {
    if (!match(value)) throw new Error(`expected ${value}`);
  };

  function parseExpression() {
    let node = parseTerm();
    while (peek() && peek().type === "symbol" && (peek().value === "+" || peek().value === "-")) {
      const op = peek().value;
      idx += 1;
      const right = parseTerm();
      node = { type: "binary", op, left: node, right };
    }
    return node;
  }

  function parseTerm() {
    let node = parseFactor();
    while (peek() && peek().type === "symbol" && (peek().value === "*" || peek().value === "/")) {
      const op = peek().value;
      idx += 1;
      const right = parseFactor();
      node = { type: "binary", op, left: node, right };
    }
    return node;
  }

  function parseFactor() {
    let node = parsePrimary();
    while (peek() && peek().type === "symbol" && peek().value === "!") {
      idx += 1;
      node = { type: "factorial", value: node };
    }
    return node;
  }

  function parsePrimary() {
    const tok = peek();
    if (!tok) throw new Error("unexpected end");
    if (tok.type === "number") {
      idx += 1;
      return { type: "number", value: tok.value };
    }
    if (tok.type === "ident") {
      idx += 1;
      const ident = tok.value;
      expect("(");
      const args = [];
      if (!match(")")) {
        args.push(parseExpression());
        while (match(",")) {
          args.push(parseExpression());
        }
        expect(")");
      }
      return { type: "func", name: ident, args };
    }
    if (tok.type === "symbol" && tok.value === "(") {
      idx += 1;
      const node = parseExpression();
      expect(")");
      return node;
    }
    throw new Error(`unexpected token: ${tok.value}`);
  }

  const ast = parseExpression();
  if (idx < tokens.length) throw new Error("extra tokens");
  return ast;
}

function toLatex(node) {
  const prec = (n) => {
    if (!n) return 0;
    if (n.type === "binary") {
      if (n.op === "+" || n.op === "-") return 1;
      if (n.op === "*" || n.op === "/") return 2;
    }
    if (n.type === "factorial" || n.type === "func") return 3;
    return 4;
  };

  const wrapIf = (child, minPrec) => {
    const latex = toLatex(child);
    return prec(child) < minPrec ? `\\left(${latex}\\right)` : latex;
  };

  if (node.type === "number") return node.value;
  if (node.type === "binary") {
    if (node.op === "/") {
      const num = toLatex(node.left);
      const den = toLatex(node.right);
      return `\\frac{${num}}{${den}}`;
    }
    const left = wrapIf(node.left, 2);
    const right = wrapIf(node.right, 2);
    if (node.op === "*") return `${left} \\cdot ${right}`;
    return `${wrapIf(node.left, 1)} ${node.op} ${wrapIf(node.right, 1)}`;
  }
  if (node.type === "factorial") {
    const child = node.value;
    const childLatex = toLatex(child);
    const needParens = child && (child.type === "factorial" || prec(child) < 3);
    const inner = needParens ? `\\left(${childLatex}\\right)` : childLatex;
    return `${inner}!`;
  }
  if (node.type === "func") {
    const arg = node.args[0] ? toLatex(node.args[0]) : "";
    if (node.name === "sqrt") return `\\sqrt{${arg}}`;
    if (node.name === "lg") return `\\lg\\left(${arg}\\right)`;
    if (node.name === "lb") return `\\mathrm{lb}\\left(${arg}\\right)`;
    if (node.name === "log" && node.args.length >= 2) {
      const base = toLatex(node.args[0]);
      const val = toLatex(node.args[1]);
      return `\\log_{${base}}\\left(${val}\\right)`;
    }
    return `\\operatorname{${node.name}}\\left(${arg}\\right)`;
  }
  return "";
}

function infixToLatex(expr) {
  try {
    const tokens = tokenize(expr);
    const ast = parseToAst(tokens);
    return toLatex(ast);
  } catch (err) {
    const safe = expr.replace(/\\/g, "\\\\").replace(/\{/g, "\\{").replace(/\}/g, "\\}");
    return `\\text{${safe}}`;
  }
}

function stripPrompt(expr) {
  let cleaned = expr.trim();
  if (cleaned.startsWith(">>>")) cleaned = cleaned.replace(/^>>>\s*/, "");
  const zhColon = cleaned.lastIndexOf("：");
  const enColon = cleaned.lastIndexOf(":");
  const cut = Math.max(zhColon, enColon);
  if (cut !== -1) cleaned = cleaned.slice(cut + 1).trim();
  const tokenMatch = cleaned.match(/(sqrt|lg|lb|log|[0-9(\-])/);
  if (tokenMatch && tokenMatch.index > 0) cleaned = cleaned.slice(tokenMatch.index).trim();
  return cleaned;
}

function extractSolutions(output, limit) {
  const solutions = [];
  const seen = new Set();
  const lines = output.split(/\r?\n/);
  for (const line of lines) {
    const marker = " = 24";
    const idx = line.lastIndexOf(marker);
    if (idx > 0) {
      const raw = line.slice(0, idx).trim();
      const expr = stripPrompt(raw);
      if (!expr || seen.has(expr)) continue;
      seen.add(expr);
      solutions.push({ infix: expr, latex: infixToLatex(expr) });
      if (limit && solutions.length >= limit) break;
    }
  }
  return solutions;
}

function runSolver(numbers, limit) {
  return new Promise((resolve, reject) => {
    if (!fs.existsSync(EXE_PATH)) {
      reject(new Error("Hegel Infix.exe not found"));
      return;
    }
    const child = spawn(EXE_PATH, [], { cwd: ROOT, windowsHide: true });
    let stdout = "";
    let stderr = "";
    const timer = setTimeout(() => {
      child.kill();
      reject(new Error("timeout"));
    }, TIMEOUT_MS);

    child.stdout.on("data", (data) => {
      stdout += data.toString("utf8");
    });
    child.stderr.on("data", (data) => {
      stderr += data.toString("utf8");
    });
    child.on("error", (err) => {
      clearTimeout(timer);
      reject(err);
    });
    child.on("close", () => {
      clearTimeout(timer);
      const solutions = extractSolutions(stdout, limit);
      resolve({ solutions, raw: stdout, stderr });
    });

    child.stdin.write(`${numbers.join(" ")}\n`);
    child.stdin.end();
  });
}

function isSafeNumber(value) {
  return Number.isInteger(value) && Number.isFinite(value) && Math.abs(value) <= 1000;
}

const server = http.createServer(async (req, res) => {
  const url = new URL(req.url, `http://${req.headers.host}`);
  if (url.pathname === "/api/solve") {
    if (req.method !== "POST") {
      sendJson(res, 405, { error: "Method not allowed" });
      return;
    }
    try {
      const body = await parseBody(req);
      const numbers = Array.isArray(body.numbers) ? body.numbers : [];
      const limit = Number.isInteger(body.limit) ? Math.min(body.limit, MAX_LIMIT) : DEFAULT_LIMIT;
      if (!numbers.length || numbers.length > MAX_NUMBERS || !numbers.every(isSafeNumber)) {
        sendJson(res, 400, { error: "Invalid numbers" });
        return;
      }
      const start = Date.now();
      const result = await runSolver(numbers, limit);
      const duration = Date.now() - start;
      sendJson(res, 200, {
        solutions: result.solutions,
        count: result.solutions.length,
        limit,
        tookMs: duration,
        stderr: result.stderr || undefined
      });
    } catch (err) {
      sendJson(res, 500, { error: err.message || "solver error" });
    }
    return;
  }

  let filePath = url.pathname === "/" ? "/index.html" : url.pathname;
  filePath = path.join(ROOT, filePath);
  if (!filePath.startsWith(ROOT)) {
    res.writeHead(403);
    res.end();
    return;
  }
  fs.readFile(filePath, (err, data) => {
    if (err) {
      res.writeHead(404);
      res.end("Not found");
      return;
    }
    const ext = path.extname(filePath).toLowerCase();
    res.writeHead(200, { "Content-Type": MIME[ext] || "application/octet-stream" });
    res.end(data);
  });
});

server.listen(PORT, () => {
  console.log(`24 Points Machine server running at http://localhost:${PORT}`);
});
