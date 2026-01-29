# WASM 构建说明

本项目使用 `Hegel Infix.cpp` 编译为 WebAssembly，前端直接调用求解引擎。

## 1) 安装 Emscripten
建议使用官方 emsdk（Windows）：

- https://emscripten.org/docs/getting_started/downloads.html

安装后确保 `em++` 在 PATH 中可用。

## 2) 生成 hegel.js / hegel.wasm
在项目根目录执行：

```
em++ "Hegel Infix.cpp" -O3 -DHEGEL_WASM \
  -s ENVIRONMENT=web \
  -s ALLOW_MEMORY_GROWTH=1 \
  -s EXPORTED_FUNCTIONS='[_hegel_solve]' \
  -s EXPORTED_RUNTIME_METHODS='["cwrap"]' \
  -o hegel.js
```

生成的 `hegel.js` 与 `hegel.wasm` 请放在项目根目录（与 `index.html` 同级）。

## 3) 本地预览
WASM 需要通过 HTTP 访问，不能直接双击打开 HTML。

任选其一：

```
python -m http.server 5173
```

或

```
npx serve .
```

访问：http://localhost:5173
