@echo off

cd /D "%~dp0"
mkdir build 2> nul
pushd build

rem set Optimization="-Ofast -march=native"
set Optimization=-O0
set Constants=-DReaWindows -DREA_INTERNAL=1 -DREA_DIAGNOSTICS=1
set Warnings=-Wall -Wunused-parameter -Wimplicit-int-float-conversion -Wno-unused-function -Wno-missing-braces -Wno-unused-parameter -Wno-unused-but-set-variable -Wno-unused-variable -Wno-switch -Wno-writable-strings -Wno-c++17-extensions -Wno-pointer-to-int-cast -Wno-tautological-constant-out-of-range-compare
set CommonCompilerFlags=-g -mavx2 --target=x86_64-pc-windows-msvc %Optimization% %Constants% %Warnings%

clang ..\code\generator.cpp -o generator.exe %CommonCompilerFlags%
pushd ..\code
..\build\generator.exe || exit 1
popd

clang -c "..\code\engine.cpp" -o engine.o %CommonCompilerFlags%
clang -c "..\code\win32_editor.cpp" -o win32_editor.o %CommonCompilerFlags%

set LinkedLibs=-l user32.lib -l Gdi32.lib -l winmm.lib
clang engine.o win32_editor.o -o win32_editor.exe %CommonCompilerFlags% %LinkedLibs% || exit 1

popd

echo build-clang.bat complete!
