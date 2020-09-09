
J?=3

all: build

build:
	@dune build @install -j $J --profile=release

install:
	@dune install

clean:
	@dune clean

TESTOPTS ?= -j 3
TESTTOOL=benchpress

test: build
	$(TESTTOOL) run -c examples/benchpress.sexp $(TESTOPTS) \
	  -t 30 --meta `git rev-parse HEAD` --progress -p smbc examples/

watch:
	@dune build -w

.PHONY: watch benchs clean build test
