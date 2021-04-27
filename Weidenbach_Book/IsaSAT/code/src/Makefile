CLANG = clang

CFLAGS = -flto -std=c11 --ld-path=`pwd`/../../clang+llvm-12.0.0-x86_64-linux-gnu-ubuntu-20.04/bin/ld.lld

all: isasat


# There is no way to print from Isabelle_LLVM
# Instead we define the printing functions in isasat.c
# and remove the empty definitions from the ll file
remove-print:
	echo "fix printing functions"
	sed -i -e '/define void @IsaSAT_Show_LLVM_print/,/}/d' isasat_restart.ll
	sed -i -e '/define void @IsaSAT_LLVM_print/,/}/d' isasat_restart.ll
	sed -i -e '/define void @IsaSAT_Profile_LLVM_start_profile/,/}/d' isasat_restart.ll
	sed -i -e '/define void @IsaSAT_Profile_LLVM_stop_profile/,/}/d' isasat_restart.ll

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
declare void @IsaSAT_LLVM_print_gc_impl(i64)\
declare void @IsaSAT_Profile_LLVM_start_profile(i8)\
declare void @IsaSAT_Profile_LLVM_stop_profile(i8)/g' \
	    isasat_restart.ll

isallvm:
#	llvm-as -disable-output isasat_no_restart.ll
	$(CLANG) $(CFLAGS) -flto -O3 isasat.c "lib_isabelle_llvm.c"  isasat_restart.ll -o isasat
