# WASM 构建说明

本项目使用 `Hegel Infix.cpp` 编译为 WebAssembly，前端直接调用求解引擎。

## 1) 依赖环境

需要安装 **Emscripten SDK (emsdk)**。
- 官方下载：https://emscripten.org/docs/getting_started/downloads.html

确保您的 emsdk 安装路径已知（默认脚本中使用 `D:\program files\emsdk\emsdk`）。

## 2) 快速编译 (推荐)

项目已提供自动编译脚本。在 Windows 环境下，直接双击运行：

```
compile.bat
```

或者在终端执行：

```powershell
.\compile.bat
```

该脚本会自动应用以下关键参数以支持大数运算：
- `MAX_FACT_ARG = 100` (支持 100! 运算)
- `MAX_EXP_SUM = 1000` (支持复杂指数链)
- 优化等级 `-O3`

## 3) 手动编译命令

如果您需要手动执行命令，请使用以下参数：

```bash
em++ "Hegel Infix.cpp" -O3 -DHEGEL_WASM \
  -s ENVIRONMENT=web \
  -s ALLOW_MEMORY_GROWTH=1 \
  -s EXPORTED_FUNCTIONS='["_hegel_solve","_hegel_configure"]' \
  -s EXPORTED_RUNTIME_METHODS='["cwrap"]' \
  -s MODULARIZE=0 \
  -o hegel.js
```

## 4) 部署

生成的 `hegel.js` 与 `hegel.wasm` 必须放在项目根目录。

本地测试请使用 HTTP 服务器（WASM 不支持 file:// 协议）：

```bash
python -m http.server
# 或
npx serve .
```

访问：http://localhost:8000
