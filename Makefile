
J?=3

all: build

build:
	@dune build @install -j $J --profile=release

install:
	@dune install

clean:
	@dune clean

TESTOPTS ?= -j 3
TESTTOOL=logitest

test: build
	@mkdir -p snapshots
	$(TESTTOOL) run -c test.toml $(TESTOPTS) \
	  --meta `git rev-parse HEAD` --summary snapshots/`date -I`.txt

watch:
	@dune build -w

PERF_CONF = test_perf.toml
perf_compare: build $(PERF_CONF)
	frogtest run -c $(PERF_CONF) # --no-caching
	frogtest plot -c $(PERF_CONF) -o perf.pdf
	frogtest csv -o perf.csv

benchs: build
	$(TESTTOOL) run -c benchmarks/smbc.toml --meta `git rev-parse HEAD`

hbmc_benchs: build
	$(TESTTOOL) run -c benchs_hbmc/conf.toml

.PHONY: watch benchs clean build test
