@echo on
call "%VSINSTALLDIR%\VC\Auxiliary\Build\vcvarsall.bat" %ARCH%
@echo on

set DMD_DIR=%cd%
if "%CONFIGURATION%" == "" set CONFIGURATION=Release
set PLATFORM=Win32
set MODEL=32mscoff
if "%ARCH%"=="x64" set PLATFORM=x64
if "%ARCH%"=="x64" set MODEL=64
set DMD=%DMD_DIR%\generated\Windows\%CONFIGURATION%\%PLATFORM%\dmd.exe

set VISUALD_INSTALLER=VisualD-%VISUALD_VER%.exe
set DMD_TESTSUITE_MAKE_ARGS=-j3
set DM_MAKE=%DMD_DIR%\dm\path\make.exe
set LDC_DIR=%DMD_DIR%\ldc2-%LDC_VERSION%-windows-multilib

FOR /F "tokens=* USEBACKQ" %%F IN (`where cl.exe`) DO (SET MSVC_CC=%%~fsF)
FOR /F "tokens=* USEBACKQ" %%F IN (`where lib.exe`) DO (SET MSVC_AR=%%~fsF)
REM this returns two lines (GNU's link.exe is on the second line)
REM Just take the first one
FOR /F "tokens=* USEBACKQ" %%F IN (`where link.exe`) DO (SET MSVC_LD=%%~fsF
  GOTO :Next)
:Next
FOR /F "tokens=* USEBACKQ" %%F IN (`where make.exe`) DO (SET GNU_MAKE=%%~fsF)

REM WORKAROUND: move files to a directory without spaces
copy "%MSVC_AR%" "%DMD_DIR%\dm\path\lib.exe"
copy "%MSVC_LD%" "%DMD_DIR%\dm\path\link.exe"
copy "%MSVC_CC%" "%DMD_DIR%\dm\path\cl.exe"
set MSVC_AR=%DMD_DIR%\dm\path\lib.exe
set MSVC_CC=%DMD_DIR%\dm\path\cl.exe
set MSVC_LD=%DMD_DIR%\dm\path\link.exe

REM expose dm_make as default make
set PATH=%DMD_DIR%\dm\path;%DMD_DIR%\tools;%PATH%
dir "%DMD_DIR%\tools"
"%DMD_DIR%\tools\grep.exe" --version
echo %PATH%
grep --version

.\%VISUALD_INSTALLER% /S
REM configure DMD path
if "%D_COMPILER%" == "dmd" reg add "HKLM\SOFTWARE\DMD" /v InstallationFolder /t REG_SZ /d "%DMD_DIR%" /reg:32 /f
REM configure LDC path
if "%D_COMPILER%" == "ldc" reg add "HKLM\SOFTWARE\LDC" /v InstallationFolder /t REG_SZ /d "%LDC_DIR%" /reg:32 /f

REM build via VS projects with LDC
cd src
if "%D_COMPILER%" == "ldc" set LDC_ARGS=%LDC_ARGS% /p:DCompiler=LDC
msbuild /target:dmd /p:Configuration=%CONFIGURATION% /p:Platform=%PLATFORM% %LDC_ARGS% vcbuild\dmd.sln || exit /B 1

%DMD% --version
grep --version

REM Check: run druntime unittests
cd "%DMD_DIR%\..\druntime"
"%DM_MAKE%" -f win64.mak MODEL=%MODEL% "DMD=%DMD%" "VCDIR=%VCINSTALLDIR%." "CC=%MSVC_CC%" "MAKE=%DM_MAKE%" target || exit /B 2
echo "[DRUNTIME] running tests..."
"%DM_MAKE%" -f win64.mak MODEL=%MODEL% "DMD=%DMD%" "VCDIR=%VCINSTALLDIR%." "CC=%MSVC_CC%" "MAKE=%DM_MAKE%" unittest || exit /B 3
"%DM_MAKE%" -f win64.mak MODEL=%MODEL% "DMD=%DMD%" "VCDIR=%VCINSTALLDIR%." "CC=%MSVC_CC%" "MAKE=%DM_MAKE%" test_all || exit /B 4

REM Check: build phobos
cd "%DMD_DIR%\..\phobos"
"%DM_MAKE%" -f win64.mak MODEL=%MODEL% "DMD=%DMD%" "VCDIR=%VCINSTALLDIR%." "CC=%MSVC_CC%" "AR=%MSVC_AR%" "MAKE=%DM_MAKE%" || exit /B 5

REM Build DMD VERSION + string imports (not built by VisualD)
copy "%DMD_DIR%\VERSION" "%DMD_DIR%\generated\Windows\Release\Win32\VERSION"

REM Run DMD testsuite
cd "%DMD_DIR%\test"
cp %DMD_DIR%\..\phobos\phobos%MODEL%.lib .
"%GNU_MAKE%" -j%NUMBER_OF_PROCESSORS% all MODEL=%MODEL% ARGS="-O -inline -g" OS=windows DMD="%DMD%" "CC=%MSVC_CC%" DMD_MODEL=%PLATFORM% BUILD=%CONFIGURATION% || exit /B 6

cd "%DMD_DIR%\..\phobos"
REM Check: build phobos unittests
if "%D_COMPILER%_%MODEL%" == "ldc_64" cp %LDC_DIR%\lib64\libcurl.dll .
if "%D_COMPILER%_%MODEL%" == "ldc_32mscoff" cp %LDC_DIR%\lib32\libcurl.dll .
if "%D_COMPILER%_%MODEL%" == "dmd_64" cp %DMD_DIR%\dmd2\windows\bin64\libcurl.dll .
if "%D_COMPILER%_%MODEL%" == "dmd_32mscoff" cp %DMD_DIR%\dmd2\windows\bin\libcurl.dll .
"%DM_MAKE%" -f win64.mak unittest MODEL=%MODEL% "DMD=%DMD%" "VCDIR=%VCINSTALLDIR%." "CC=%MSVC_CC%" "MAKE=%DM_MAKE%"
