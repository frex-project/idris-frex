all: build

build:
	idris2 --build tests.ipkg

run: $(patsubst frextests/%,run-%,$(wildcard frextests/*))

run-%:
	@echo running $*
	./build/exec/runtests idris2 --failure-file failures --only $*

.PHONY: all build run
