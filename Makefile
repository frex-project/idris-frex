IDRIS2 ?= idris2

all: build

build:
	${IDRIS2} --build frex.ipkg

install:
	${IDRIS2} --install frex.ipkg

doc:
	${IDRIS2} --mkdoc frex.ipkg

clean:
	${IDRIS2} --clean frex.ipkg

test:
	@${MAKE} -C tests build run

deepclean:
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;

.PHONY: all build install clean doc test deepclean
