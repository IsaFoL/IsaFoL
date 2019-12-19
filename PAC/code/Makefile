MLTON=mlton

all: pasteque


pasteque: *.sml *.mlb
	$(MLTON) -inline 1500 pasteque.mlb

profile: *.sml *.mlb
	$(MLTON) -profile time pasteque.mlb

llvm: *.sml *.mlb
	$(MLTON) -verbose 1 -const 'MLton.safe false' -default-type int64 -output pasteque -codegen llvm -inline 1500 -cc-opt -fPIC -as-opt --relocation-model=pic -link-opt -fPIC -llvm-llc-opt '--relocation-model=pic -O3' -llvm-opt-opt --relocation-model=pic pasteque.mlb
clean:
	rm -rf pasteque