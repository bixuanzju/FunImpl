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

.PHONY : doc
doc:
	make -C doc

.PHONY : proof
proof:
	make -C proof

.PHONY : clean
clean :
	rm -f $(srcdir)/Parser.hs
	make -C doc clean
	make -C proof clean

.PHONY : distclean
distclean : clean
	cabal clean
	make -C doc distclean
