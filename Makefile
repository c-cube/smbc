
OCAMLBUILD=ocamlbuild -use-ocamlfind -tag debug
TARGETS=src/smbc.byte src/smbc.native
BINDIR ?= /usr/bin/

all: build

build:
	$(OCAMLBUILD) $(TARGETS)

clean:
	$(OCAMLBUILD) -clean

TESTOPTS ?= -j 3
TESTTOOL=logitest

install: build
	cp smbc.native $(BINDIR)/smbc

test: build
	@mkdir -p snapshots
	$(TESTTOOL) run -c test.toml $(TESTOPTS) \
	  --meta `git rev-parse HEAD` --summary snapshots/`date -I`.txt

watch:
	while find src/ -print0 | xargs -0 inotifywait -e delete_self -e modify ; do \
		echo "============ at `date` ==========" ; \
		sleep 0.1; \
		make all; \
	done

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
