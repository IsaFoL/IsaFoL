MLTON = mlton
CLANG = clang

CFLAGS = -flto -std=c11 -Wall -Wextra 

all: isasat

isasat:
	$(MLTON) -const 'MLton.safe false' -verbose 1 -default-type int64 -output IsaSAT -codegen native -inline 700 -cc-opt -O3 IsaSAT.mlb

bounded:
	$(MLTON) -const 'MLton.safe false' -verbose 1 -default-type int64 -output IsaSAT_bounded -codegen native -inline 700 -cc-opt -O3 IsaSAT_bounded.mlb


example:
	echo "\nsimply print the SAT or UNSAT:\n\n" &&	./IsaSAT AProVE09-21.cnf && echo "\n\n"
	echo "\n\nwith the model:\n" && ./IsaSAT --verbose AProVE09-21.cnf

# There is no way to print from Isabelle_LLVM
# Instead we define the printing functions in isasat.c
# and remove the empty definitions from the ll file
remove-print:
	echo "fix printing functions"
	sed -i -e '/define void @IsaSAT_Show_LLVM_print/,/}/d' isasat_restart.ll
	sed -i -e '/define void @IsaSAT_LLVM_print/,/}/d' isasat_restart.ll
	sed -i -e 's/declare i8\* @isabelle_llvm_calloc(i64, i64)/declare i8* @isabelle_llvm_calloc(i64, i64)\
declare void @IsaSAT_Show_LLVM_print_c_impl(i64)\
declare void @IsaSAT_Show_LLVM_print_char_impl(i64)\
declare void @IsaSAT_Show_LLVM_print_uint64_impl(i64)\
declare void @IsaSAT_Show_LLVM_print_open_colour_impl(i64)\
declare void @IsaSAT_Show_LLVM_print_close_colour_impl(i64)\
declare void @IsaSAT_LLVM_print_propa_impl(i64)\
declare void @IsaSAT_LLVM_print_confl_impl(i64)\
declare void @IsaSAT_LLVM_print_dec_impl(i64)\
declare void @IsaSAT_LLVM_print_res_impl(i64)\
declare void @IsaSAT_LLVM_print_lres_impl(i64)\
declare void @IsaSAT_LLVM_print_uset_impl(i64)\
declare void @IsaSAT_LLVM_print_gc_impl(i64)/g' \
	    isasat_restart.ll

llvm:
	$(MLTON) -verbose 1 -const 'MLton.safe false' -default-type int64 -output IsaSAT -codegen llvm -inline 700 -cc-opt -fPIC -as-opt --relocation-model=pic -link-opt -fPIC -llvm-llc-opt '--relocation-model=pic -O3' -llvm-opt-opt --relocation-model=pic IsaSAT.mlb

clean:
	rm -f IsaSAT IsaSAT_restart *.profdata *.prof *.profraw

isallvm:
#	llvm-as -disable-output isasat_no_restart.ll
	$(CLANG) $(CFLAGS) -flto -O3 isasat.c "lib_isabelle_llvm.c"  isasat_restart.ll -o isasat_llvm

isallvm-prof:
#	llvm-as -disable-output isasat_no_restart.ll
	$(CLANG) -std=c11 -Wall -Wextra -inline-threshold=6000 -O2 -lprofiler isasat.c "lib_isabelle_llvm.c"  isasat_restart.ll -o isasat_llvm


isallvm-sanit:
#	llvm-as -disable-output isasat_no_restart.ll
	$(CLANG) $(CFLAGS) -fsanitize=undefined -fsanitize=address -fno-sanitize-recover=undefined -Wall -Wextra -g isasat.c "lib_isabelle_llvm.c" isasat_restart.ll -o isasat_llvm

isallvm-gdb:
	$(CLANG) -std=c11 -O2 -g -Wall -Wextra -g isasat.c "lib_isabelle_llvm.c"  isasat_restart.ll isasat_wrapper.ll -o isasat_llvm
