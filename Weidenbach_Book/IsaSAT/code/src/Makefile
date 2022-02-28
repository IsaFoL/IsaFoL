CLANG = clang

CFLAGS = -std=c11 #-ftlo

all: isallvm


# There is no way to print from Isabelle_LLVM
# Instead we define the printing functions in isasat.c
# and remove the empty definitions from the ll file
remove-print:
	echo "fix printing functions"
	sed -i -e '/define void @IsaSAT_LLVM_print_gc_impl/,/}/d' isasat_restart.ll
	sed -i -e '/define void @IsaSAT_LLVM_print_irred_clss_impl/,/}/d' isasat_restart.ll
	sed -i -e '/define void @IsaSAT_LLVM_print_uset_impl/,/}/d' isasat_restart.ll
	sed -i -e '/define void @IsaSAT_LLVM_print_lres_impl/,/}/d' isasat_restart.ll
	sed -i -e '/define void @IsaSAT_LLVM_print_res_impl/,/}/d' isasat_restart.ll
	sed -i -e '/define void @IsaSAT_LLVM_print_dec_impl/,/}/d' isasat_restart.ll
	sed -i -e '/define void @IsaSAT_LLVM_print_confl_impl/,/}/d' isasat_restart.ll
	sed -i -e '/define void @IsaSAT_LLVM_print_propa_impl/,/}/d' isasat_restart.ll
	sed -i -e '/define void @IsaSAT_Show_LLVM_print_c_impl/,/}/d' isasat_restart.ll
	sed -i -e '/define void @IsaSAT_Show_LLVM_print_char_impl/,/}/d' isasat_restart.ll
	sed -i -e '/define void @IsaSAT_Show_LLVM_print_uint64_impl/,/}/d' isasat_restart.ll
	sed -i -e '/define void @IsaSAT_Show_LLVM_print_open_colour_impl/,/}/d' isasat_restart.ll
	sed -i -e '/define void @IsaSAT_Show_LLVM_print_close_colour_impl/,/}/d' isasat_restart.ll
#	sed -i -e '/define void @IsaSAT_Show_LLVM_print /,/}/d' isasat_restart.ll
#	sed -i -e '/define void @IsaSAT_LLVM_print /,/}/d' isasat_restart.ll
	sed -i -e '/define void @IsaSAT_Profile_LLVM_start_profile/,/}/d' isasat_restart.ll
	sed -i -e '/define void @IsaSAT_Profile_LLVM_stop_profile/,/}/d' isasat_restart.ll
	sed -i -e '/define void @IsaSAT_Setup3_LLVM_print_encoded_lit_code/,/}/d' isasat_restart.ll
	sed -i -e '/define void @IsaSAT_Setup3_LLVM_print_encoded_lit_end_code/,/}/d' isasat_restart.ll
	sed -i -e '/define void @IsaSAT_Setup3_LLVM_print_literal_of_trail_code/,/}/d' isasat_restart.ll


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
declare void @IsaSAT_LLVM_print_irred_clss_impl(i64)\
declare void @IsaSAT_Profile_LLVM_start_profile(i8)\
declare void @IsaSAT_Profile_LLVM_stop_profile(i8)\
declare void @IsaSAT_Setup3_LLVM_print_encoded_lit_code(i32)\
declare void @IsaSAT_Setup3_LLVM_print_encoded_lit_end_code(i32)\
declare void @IsaSAT_Setup3_LLVM_print_literal_of_trail_code(i32)/g' \
	    isasat_restart.ll

isallvm:
	#llvm-as -disable-output isasat_restart.ll
	$(CLANG) $(CFLAGS) -DPRINTSTATS=1 -O3 -flto isasat.c "lib_isabelle_llvm.c"  isasat_restart.ll -o isasat

competition:
	$(CLANG) $(CFLAGS) -DNOOPTIONS=1 -DNOPROFILING -flto -O3 isasat.c "lib_isabelle_llvm.c"  isasat_restart.ll -o isasat

clean:
	rm -rf isasat
