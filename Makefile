
J?=3
OPTS ?= --profile=release
all: build

build:
	@dune build @install -j $J $(OPTS)

install:
	@dune install

clean:
	@dune clean

TESTOPTS ?= -j 3
TESTTOOL=benchpress

test: build
	$(TESTTOOL) run -c examples/benchpress.sexp $(TESTOPTS) \
	  -t 30 --meta `git rev-parse HEAD` --progress -p smbc examples/

WATCH ?= @all
watch:
	@dune build $(WATCH) $(OPTS) -w

.PHONY: watch benchs clean build test
