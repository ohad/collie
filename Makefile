PROJECT=collie

all: build

build:
	idris2 --build collie.ipkg

install:
	idris2 --install collie.ipkg

install-with-src:
	idris2 --install-with-src collie.ipkg

doc:
	idris2 --mkdoc collie.ipkg

clean:
	idris2 --clean collie.ipkg

test:
	@${MAKE} -C tests build run

deepclean:
	@find . -type f -name '*.ttc' -exec rm -f {} \;
	@find . -type f -name '*.ttm' -exec rm -f {} \;
	@find . -type f -name '*.ibc' -exec rm -f {} \;

.PHONY: all build install clean doc test deepclean
