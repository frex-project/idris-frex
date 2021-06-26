all: build

build:
	idris2 --build frex.ipkg

install:
	idris2 --install frex.ipkg

doc:
	idris2 --mkdoc frex.ipkg

.PHONY: all build install doc
