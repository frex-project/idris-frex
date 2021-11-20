INTERACTIVE ?= --interactive
IDRIS2 ?= idris2

all: build

build:
	${IDRIS2} --build tests.ipkg

run:
	./build/exec/runtests ${IDRIS2} $(INTERACTIVE) --failure-file failures

.PHONY: all build run
