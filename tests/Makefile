INTERACTIVE ?= --interactive

all: build

build:
	idris2 --build tests.ipkg

run:
	./build/exec/runtests idris2 $(INTERACTIVE) --failure-file failures

.PHONY: all build run
