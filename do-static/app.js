const input = document.getElementById("numbers-input");
const output = document.getElementById("output");
const emptyState = document.getElementById("empty-state");
const status = document.getElementById("status");
const countBadge = document.getElementById("count-badge");
const solveBtn = document.getElementById("solve-btn");
const limitSelect = document.getElementById("limit-select");
const settingsPanel = document.getElementById("settings-panel");
const settingsToggle = document.getElementById("settings-toggle");
const cardCountSelect = document.getElementById("card-count");
const maxNumberInput = document.getElementById("max-number");
const minNumberInput = document.getElementById("min-number");
const randomBtn = document.getElementById("random-btn");
const rulesBtn = document.getElementById("rules-btn");
const rulesContainer = document.querySelector(".rules-container");
const exampleButtons = document.querySelectorAll(".example-btn");

// Settings Toggle Logic
if (settingsToggle && settingsPanel) {
  settingsToggle.addEventListener("click", (e) => {
    e.stopPropagation();
    settingsPanel.classList.toggle("collapsed");
    // Close rules if open
    if (rulesContainer) rulesContainer.classList.remove("active");
  });
}

// Rules Toggle Logic
if (rulesBtn && rulesContainer) {
  rulesBtn.addEventListener("click", (e) => {
    e.stopPropagation();
    rulesContainer.classList.toggle("active");
    // Close settings if open
    if (settingsPanel) settingsPanel.classList.add("collapsed");
  });
}

// Click outside to close both
document.addEventListener("click", (e) => {
  if (rulesContainer && !rulesContainer.contains(e.target)) {
    rulesContainer.classList.remove("active");
  }
  if (settingsPanel && settingsToggle && 
      !settingsPanel.contains(e.target) && !settingsToggle.contains(e.target)) {
    settingsPanel.classList.add("collapsed");
  }
});

// Advanced inputs
const targetInput = document.getElementById("target-input");
const maxNestInput = document.getElementById("max-nest");
const maxSqrtInput = document.getElementById("max-sqrt");
const maxFactInput = document.getElementById("max-fact");
const maxLgInput = document.getElementById("max-lg");
const maxLbInput = document.getElementById("max-lb");
const maxLogInput = document.getElementById("max-log");
const noNegInput = document.getElementById("no-neg");
const onlyMathInput = document.getElementById("only-math");

let wasmSolve = null;
let wasmConfig = null;
let wasmReady = false;

function parseNumbers(value) {
  return value
    .split(/[\s,]+/)
    .map((part) => part.trim())
    .filter(Boolean)
    .map((part) => Number(part))
    .filter((num) => Number.isInteger(num));
}

function setStatus(message) {
  status.textContent = message;
}

function updateCount(count) {
  countBadge.textContent = `${count} 条`;
}

function clearOutput() {
  output.innerHTML = "";
  emptyState.hidden = false;
  updateCount(0);
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
      const unary =
        !prev ||
        (prev.type === "symbol" && (prev.value === "(" || prev.value === "," || "+-*/".includes(prev.value)));
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

function renderSolutions(lines) {
  output.innerHTML = "";
  if (!lines.length) {
    emptyState.hidden = false;
    return;
  }
  emptyState.hidden = true;

  lines.forEach((expr, index) => {
    const row = document.createElement("div");
    row.className = "formula-line";

    const badge = document.createElement("div");
    badge.className = "line-no";
    badge.textContent = String(index + 1).padStart(2, "0");

    const math = document.createElement("div");
    math.className = "math";

    try {
      const targetVal = targetInput.value || "24";
      window.katex.render(infixToLatex(expr) + " = " + targetVal, math, {
        displayMode: true,
        throwOnError: false,
        strict: "ignore"
      });
    } catch (error) {
      row.classList.add("error");
      math.textContent = expr;
    }

    row.append(badge, math);
    output.appendChild(row);
  });
}

function parseOutput(raw) {
  return raw
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter(Boolean)
    .map((line) => {
      const idx = line.lastIndexOf(" = ");
      return idx > 0 ? line.slice(0, idx).trim() : "";
    })
    .filter(Boolean);
}

function initWasm() {
  if (!window.Module || !Module.cwrap) {
    setStatus("WASM 未加载，请先生成 hegel.js / hegel.wasm。", "warn");
    return;
  }
  wasmSolve = Module.cwrap("hegel_solve", "string", ["string", "number"]);
  // void hegel_configure(int target, int max_nest, int max_sqrt, int max_fact, int max_lg, int max_lb, int max_log, int no_neg, int only_math)
  wasmConfig = Module.cwrap("hegel_configure", "void", ["number", "number", "number", "number", "number", "number", "number", "number", "number"]);
  wasmReady = true;
  setStatus("WASM 已就绪。输入数字开始计算。");
}

function attachWasmReady() {
  if (window.Module && Module.calledRun) {
    initWasm();
    return;
  }
  if (window.Module) {
    Module.onRuntimeInitialized = () => {
      initWasm();
    };
  } else {
    setStatus("WASM 模块未加载，请检查 hegel.js 是否存在。", "warn");
  }
}

// Solves the puzzle for given numbers string, returning array of solution lines or empty array
function getSolutions(numbersStr, limitVal) {
  if (!wasmReady || !wasmSolve) return [];
  try {
    const raw = wasmSolve(numbersStr, limitVal);
    return parseOutput(raw || "");
  } catch (err) {
    console.error(err);
    return [];
  }
}

function solve() {
  if (!wasmReady || !wasmSolve) {
    setStatus("WASM 尚未就绪，请稍候。", "warn");
    return;
  }

  const numbers = parseNumbers(input.value);
  if (numbers.length < 2 || numbers.length > 8) {
    setStatus("请输入 2~8 个整数。", "warn");
    clearOutput();
    return;
  }

  setStatus("计算中，请稍候…");
  solveBtn.disabled = true;

  // Use a timeout to allow UI to update (show "Calculation...") before heavy work
  setTimeout(() => {
      try {
        // Configure WASM before solve
        if (wasmConfig) {
            wasmConfig(
                parseInt(targetInput.value) || 24,
                parseInt(maxNestInput.value) || 4,
                parseInt(maxSqrtInput.value) || 0, // default 0 if empty/nan, but HTML default is 2
                parseInt(maxFactInput.value) || 0,
                parseInt(maxLgInput.value) || 0,
                parseInt(maxLbInput.value) || 0,
                parseInt(maxLogInput.value) || 0,
                noNegInput.checked ? 1 : 0,
                onlyMathInput.checked ? 1 : 0
            );
        }

        const line = numbers.join(" ");
      const limit = Number(limitSelect.value);
      const lines = getSolutions(line, limit);

      updateCount(lines.length);
      renderSolutions(lines);

      if (!lines.length) {
        setStatus("没有找到解。请尝试调整数字。");
      } else {
        const tip = lines.length >= limit ? "（已截断显示）" : "";
        setStatus(`完成，找到 ${lines.length} 条 ${tip}`.trim());
      }
    } catch (err) {
      setStatus(`出错：${err.message}`);
      clearOutput();
    } finally {
      solveBtn.disabled = false;
    }
  }, 10);
}

solveBtn.addEventListener("click", solve);
input.addEventListener("keydown", (event) => {
  if (event.key === "Enter") {
    event.preventDefault();
    solve();
  }
});

exampleButtons.forEach((btn) => {
  btn.addEventListener("click", () => {
    input.value = btn.dataset.value;
    solve();
  });
});



// Smart Random Generator
randomBtn.addEventListener("click", () => {
  if (!wasmReady) {
    setStatus("WASM 未就绪，无法生成。", "warn");
    return;
  }

  const count = parseInt(cardCountSelect.value, 10) || 4;
  const max = parseInt(maxNumberInput.value, 10) || 13;

  // Attempt to find a solvable puzzle (max 10 retries)
  const MAX_RETRIES = 10;
  let candidates = [];
  let foundSolvable = false;

  // Show loading state
  randomBtn.disabled = true;
  randomBtn.innerHTML = '<span class="icon">⏳</span> 生成中...';

  // Async to let UI render the loading state
  setTimeout(() => {
    for (let attempt = 0; attempt < MAX_RETRIES; attempt++) {
      const nums = [];
      const minVal = parseInt(minNumberInput.value, 10) || 1;
      const maxVal = parseInt(maxNumberInput.value, 10) || 80; // Default to 80 as requested
      
      // Validation: Ensure min <= max
      const actualMin = Math.min(minVal, maxVal);
      const actualMax = Math.max(minVal, maxVal);

      for (let i = 0; i < count; i++) {
        nums.push(Math.floor(Math.random() * (actualMax - actualMin + 1)) + actualMin);
      }

      // Fast check (limit=1 just to check existence)
      // Just check if it returns > 0 lines.
      // Note: In some C++ configs limit might be strict, but usually WASM returns string.
      // We use a small limit for speed check.
      const line = nums.join(" ");
      const solutions = getSolutions(line, 1);

      candidates = nums;
      if (solutions.length > 0) {
        foundSolvable = true;
        break;
      }
    }

    input.value = candidates.join(" ");
    randomBtn.disabled = false;
    randomBtn.innerHTML = '<span class="icon">🎲</span> 随机发牌';

    solve(); // This will run the full solve

    if (!foundSolvable) {
      // Overwrite status after solve() potentially sets it
      // Actually solve() runs async in timeout, so we should rely on solve() to say "No solution" 
      // but we can hint user.
      // But since we call solve() and solve() is async (setTimeout 10), 
      // our toast here might be overwritten. 
      // It's fine, solve() will faithfully report "No result" if we really failed 10 times.
    }
  }, 10);
});

clearOutput();
attachWasmReady();
