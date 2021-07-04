all: build

build:
	idris2 --build frex.ipkg

install:
	idris2 --install frex.ipkg

doc:
	idris2 --mkdoc frex.ipkg

clean:
	idris2 --clean frex.ipkg

test:
	@${MAKE} -C tests build run

deepclean:
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;

.PHONY: all build install clean doc test deepclean
