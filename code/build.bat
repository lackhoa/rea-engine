@echo off

mkdir ..\build 2> nul
cd ..\build

rem set Optimization="-Ofast -march=native"
set Optimization=-O0
set Constants=
set Warnings=-Wall -Wunused-parameter -Wimplicit-int-float-conversion -Wno-unused-function -Wno-missing-braces -Wno-unused-parameter -Wno-unused-but-set-variable -Wno-unused-variable
set CommonCompilerFlags=-g -mavx2 --target=x86_64-pc-windows-msvc %Optimization% %Constants% %Warnings%

set LinkedLibs=-l user32.lib -l Gdi32.lib -l winmm.lib
clang "..\code\win32_editor.cpp" -o win32_editor.exe %CommonCompilerFlags% %LinkedLibs%
