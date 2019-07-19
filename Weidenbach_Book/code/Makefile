MLTON = mlton
CLANG = clang

all: isasat

isasat:
	$(MLTON) -const 'MLton.safe false' -verbose 1 -default-type int64 -output IsaSAT -codegen native -inline 700 -cc-opt -O3 IsaSAT.mlb

bounded:
	$(MLTON) -const 'MLton.safe false' -verbose 1 -default-type int64 -output IsaSAT_bounded -codegen native -inline 700 -cc-opt -O3 IsaSAT_bounded.mlb


example:
	echo "\nsimply print the SAT or UNSAT:\n\n" &&	./IsaSAT AProVE09-21.cnf && echo "\n\n"
	echo "\n\nwith the model:\n" && ./IsaSAT --verbose AProVE09-21.cnf

llvm:
	$(MLTON) -verbose 1 -const 'MLton.safe false' -default-type int64 -output IsaSAT -codegen llvm -inline 700 -cc-opt -fPIC -as-opt --relocation-model=pic -link-opt -fPIC -llvm-llc-opt '--relocation-model=pic -O3' -llvm-opt-opt --relocation-model=pic IsaSAT.mlb

clean:
	rm -f IsaSAT IsaSAT_restart *.profdata *.prof *.profraw

isallvm:
#	llvm-as -disable-output isasat_no_restart.ll
	$(CLANG) -std=c11 -O3 -Wall -Wextra isasat.c "lib_isabelle_llvm.c" isasat_no_restart.ll -o isasat_llvm

isallvm-prof:
#	llvm-as -disable-output isasat_no_restart.ll
	$(CLANG) -std=c11 -O2 -lprofiler -g -fprofile-generate -Wall -Wextra isasat.c "lib_isabelle_llvm.c" isasat_no_restart.ll -o isasat_llvm


isallvm-sanit:
#	llvm-as -disable-output isasat_no_restart.ll
	$(CLANG) -std=c11 -g -fsanitize=undefined -fsanitize=address -fno-sanitize-recover=undefined -Wall -Wextra -g isasat.c "lib_isabelle_llvm.c" isasat_no_restart.ll -o isasat_llvm

isallvm-gdb:
	$(CLANG) -std=c11 -O0 -g -Wall -Wextra -g isasat.c "lib_isabelle_llvm.c" isasat_no_restart.ll -o isasat_llvm
