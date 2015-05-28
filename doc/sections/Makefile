OTT_FILES = expcore.ott
OTT_OPTS  = -tex_show_meta false
TARGETS   = overview.tex explicitcore.tex recursion.tex

WARN_MSG = "%%% !!! WARNING: AUTO GENERATED. DO NOT MODIFY !!! %%%"

all: $(TARGETS) $(OTT_FILES:.ott=.ott.tex)

%.ott.tex: %.ott
	ott -tex_wrap false $(OTT_OPTS) -o $@ $^

%.tex: %.mng.tex $(OTT_FILES)
	ott $(OTT_OPTS) -tex_filter $< $@ $(OTT_FILES)
	@echo $(WARN_MSG) | cat - "$@" | tee "$@" >/dev/null

.PHONY: all clean
clean:
	rm -f *.ott.tex $(TARGETS)
