@echo off

cd /D "%~dp0"
call build-clang
rem call build-msvc

pushd code
rem ..\build\win32_editor.exe || exit 1
popd
