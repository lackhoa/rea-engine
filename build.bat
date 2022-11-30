@echo off

cd /D "%~dp0"
call build-clang %1
rem call build-msvc

pushd data
..\build\win32_editor.exe  || exit 1
popd
