MLTON = mlton

all: isasat

isasat:
	$(MLTON) -const 'MLton.safe false' -verbose 1 -default-type int64 -output IsaSAT -codegen native -inline 700 -cc-opt -O3 IsaSAT.mlb

example:
	echo "\nsimply print the SAT or UNSAT:\n\n" &&	./IsaSAT AProVE09-21.cnf && echo "\n\n"
	echo "\n\nwith the model:\n" && ./IsaSAT --verbose AProVE09-21.cnf

llvm:
	$(MLTON) -verbose 1 -const 'MLton.safe false' -default-type int64 -output IsaSAT -codegen llvm -inline 700 -cc-opt -fPIC -as-opt --relocation-model=pic -link-opt -fPIC -llvm-llc-opt '--relocation-model=pic -O3' -llvm-opt-opt --relocation-model=pic IsaSAT.mlb

clean:
	rm -f IsaSAT IsaSAT_restart