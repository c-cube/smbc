
OCAMLBUILD=ocamlbuild -use-ocamlfind -tag debug
TARGETS=src/smbc.native src/smbc.byte

all: build

build:
	$(OCAMLBUILD) $(TARGETS)

clean:
	$(OCAMLBUILD) -clean

watch:
	while find src/ -print0 | xargs -0 inotifywait -e delete_self -e modify ; do \
		echo "============ at `date` ==========" ; \
		sleep 0.1; \
		make all; \
	done
