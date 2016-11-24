#!/usr/bin/env bash

$@ &

while jobs | grep Running > /dev/null ; do
  sleep 0.1
  kill -s USR1 %1
  I=$(( $I + 1 ))
done
