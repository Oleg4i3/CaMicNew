@if "%DEBUG%"=="" @echo off
@rem Gradle startup script for Windows
@rem Auto-generated
set DIRNAME=%~dp0
if "%DIRNAME%"=="" set DIRNAME=.
java %GRADLE_OPTS% -classpath "%DIRNAME%\gradle\wrapper\gradle-wrapper.jar" org.gradle.wrapper.GradleWrapperMain %*
