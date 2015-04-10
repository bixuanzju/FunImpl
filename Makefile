srcdir=src
parsefile=Parser.y

.PHONY: all
all: parser
	cabal install  --enable-tests

.PHONY : repl
repl : parser
	cabal run

.PHONY : test
test : parser
	cabal test

parser : $(srcdir)/$(parsefile)
	cd $(srcdir) && happy $(parsefile)

.PHONY : clean
clean :
	rm $(srcdir)/Parser.hs
