OTT_FILES = expcore.ott
OTT_TEX   = expcore.tex
OTT_OPTS  = -tex_show_meta false
TARGET    = explicitcore

all: $(TARGET).tex $(OTT_TEX)

$(TARGET).tex: $(TARGET).mng $(OTT_FILES)
	ott $(OTT_OPTS) -tex_filter $< $@ $(OTT_FILES)

$(OTT_TEX): $(OTT_FILES)
	ott -tex_wrap false $(OTT_OPTS) -o $@ $^

.PHONY: all clean
clean:
	rm -f $(OTT_TEX) $(TARGET).tex
