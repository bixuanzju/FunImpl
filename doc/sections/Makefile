OTT_FILES = expcore.ott
OTT_TEX   = expcore.tex
OTT_OPTS  = -tex_show_meta false
TARGET_S2    = overview
TARGET_S3    = explicitcore

WARN_MSG = "%%% !!! WARNING: AUTO GENERATED. DO NOT MODIFY !!! %%%"

all: $(TARGET_S2).tex $(TARGET_S3).tex $(OTT_TEX)

$(TARGET_S2).tex: $(TARGET_S2)-template.tex $(OTT_FILES)
	ott $(OTT_OPTS) -tex_filter $< $@ $(OTT_FILES)
	@echo $(WARN_MSG) | cat - "$@" | tee "$@" >/dev/null

$(TARGET_S3).tex: $(TARGET_S3)-template.tex $(OTT_FILES)
	ott $(OTT_OPTS) -tex_filter $< $@ $(OTT_FILES)
	@echo $(WARN_MSG) | cat - "$@" | tee "$@" >/dev/null

$(OTT_TEX): $(OTT_FILES)
	ott -tex_wrap false $(OTT_OPTS) -o $@ $^

.PHONY: all clean
clean:
	rm -f $(OTT_TEX) $(TARGET_S2).tex $(TARGET_S3).tex
