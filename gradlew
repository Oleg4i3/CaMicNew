#!/bin/sh
# Gradle start-up script for POSIX systems
APP_HOME=$(dirname "$(readlink -f "$0")" 2>/dev/null || pwd)
exec java $GRADLE_OPTS \
  -classpath "$APP_HOME/gradle/wrapper/gradle-wrapper.jar" \
  org.gradle.wrapper.GradleWrapperMain "$@"
