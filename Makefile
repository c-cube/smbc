
OCAMLBUILD=ocamlbuild -use-ocamlfind
TARGETS=src/e3.native

all: build

build:
	$(OCAMLBUILD) $(TARGETS)

clean:
	$(OCAMLBUILD) -clean

watch:
	while find src/ -print0 | xargs -0 inotifywait -e delete_self -e modify ; do \
		echo "============ at `date` ==========" ; \
		make all; \
	done
