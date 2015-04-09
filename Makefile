srcdir=src
parsers=Parser.hs

.PHONY: all
all: parsers
	cabal install  --enable-tests

.PHONY : repl
repl :
	cabal run

.PHONY : test
test : parsers
	cabal test

.PHONY : parsers
parsers :
	cd $(srcdir) && happy Parser.y

.PHONY : clean
clean :
	rm $(srcdir)/$(parsers)
