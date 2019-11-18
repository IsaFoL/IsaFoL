MLON=mlton

all: pactrim


pactrim: *.sml *.mlb
	$(MLTON)  mlton -inline 700 pactrim.mlb

profile: *.sml *.mlb
	$(MLTON)  mlton -profile time pactrim.mlb

clean:
	rm -rf pactrim