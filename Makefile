srcdir=src
parsers=Parser.hs

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
