Core = Core
Lib = SfLib

all: $(Core).vo

$(Core).vo : $(Lib).vo
	coqc $(Core).v

$(Lib).vo :
	coqc $(Lib).v

clean:
	rm *.vo *.glob
