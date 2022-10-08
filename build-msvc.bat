@echo off

cd /D "%~dp0"
mkdir build 2> nul
cd build

set Optimization=-Od
set Constants=-DReaWindows
set Warnings=-MTd -Gm- -GR- -EHsc -EHa- -FC -nologo -Z7 -WX -W4 -wd4100 -wd4101 -wd4189 -wd4201 -wd4459 -wd4456 -wd4457 -wd4505 -wd4068 -wd4702 -wd4127
set CommonCompilerFlags=-arch:AVX2 -std:c++17 %Optimization% %Constants% %Warnings%

rem cl ..\code\generator.cpp %CommonCompilerFlags%
rem pushd ..\code
rem ..\build\generator.exe
rem popd

cl -c "..\code\engine.cpp" %CommonCompilerFlags%
cl -c "..\code\win32_editor.cpp" %CommonCompilerFlags%

set LinkerFlags=-link -incremental:no -opt:ref user32.lib Gdi32.lib winmm.lib
cl win32_editor.obj engine.obj %CommonCompilerFlags% %LinkerFlags%

pushd ..\code
..\build\win32_editor.exe || exit 1
popd
