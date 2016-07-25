#!/usr/bin/env bash

BIN=./smbc.native

perf record --call-graph=dwarf "$BIN" $@

perf script \
  | stackcollapse-perf --kernel \
  | sed 's/caml//g' \
  | flamegraph > perf.svg

