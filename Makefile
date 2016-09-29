
OCAMLBUILD=ocamlbuild -use-ocamlfind -tag debug
TARGETS=src/smbc.native src/smbc.byte
BINDIR ?= /usr/bin/

all: build

build:
	$(OCAMLBUILD) $(TARGETS)

clean:
	$(OCAMLBUILD) -clean

install: build
	cp smbc.native $(BINDIR)/smbc

test: build
	frogtest run -c test.toml --meta `git rev-parse HEAD`

watch:
	while find src/ -print0 | xargs -0 inotifywait -e delete_self -e modify ; do \
		echo "============ at `date` ==========" ; \
		sleep 0.1; \
		make all; \
	done

benchs:
	frogtest run -c benchmarks/smbc.toml --meta `git rev-parse HEAD`

.PHONY: watch benchs clean build test
