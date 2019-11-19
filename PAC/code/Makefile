MLTON=mlton

all: pactrim


pactrim: *.sml *.mlb
	$(MLTON) -inline 1500 pactrim.mlb

profile: *.sml *.mlb
	$(MLTON) -profile time pactrim.mlb

llvm: *.sml *.mlb
	$(MLTON) -verbose 1 -const 'MLton.safe false' -default-type int64 -output pactrim -codegen llvm -inline 1500 -cc-opt -fPIC -as-opt --relocation-model=pic -link-opt -fPIC -llvm-llc-opt '--relocation-model=pic -O3' -llvm-opt-opt --relocation-model=pic pactrim.mlb
clean:
	rm -rf pactrim