@echo off
if not exist "D:\program files\emsdk\emsdk\emsdk_env.bat" (
    echo Error: emsdk_env.bat not found at D:\program files\emsdk\emsdk\emsdk_env.bat
    pause
    exit /b 1
)
call "D:\program files\emsdk\emsdk\emsdk_env.bat"
echo Compiling...
em++ -O3 -s WASM=1 -s "EXPORTED_RUNTIME_METHODS=['cwrap']" -s "EXPORTED_FUNCTIONS=['_hegel_solve','_hegel_configure']" -s MODULARIZE=0 -s ENVIRONMENT=web -s ALLOW_MEMORY_GROWTH=1 -DHEGEL_WASM -o hegel.js "Hegel Infix.cpp"
if %errorlevel% neq 0 (
    echo Compilation failed!
    pause
) else (
    echo Compilation successful!
)
