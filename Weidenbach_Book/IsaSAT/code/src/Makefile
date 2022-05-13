CLANG = clang

# higher inlining level is necessary since moving to
# the new state
CFLAGS = -std=c11 -flto -mllvm -inline-threshold=4000 -Omtune=native -Omarch=native

all: isallvm


# There is no way to print from Isabelle_LLVM
# Instead we define the printing functions in isasat.c
# and remove the empty definitions from the ll file
remove-print:
	echo "fix printing functions"
	sed -i -e '/define void @IsaSAT_LLVM_print_gc_impl/,/}/d' \
	  -e '/define void @IsaSAT_LLVM_print_irred_clss_impl/,/}/d' \
	  -e '/define void @IsaSAT_LLVM_print_binary_unit_impl/,/}/d' \
	  -e '/define void @IsaSAT_LLVM_print_binary_red_removed_impl/,/}/d' \
	  -e '/define void @IsaSAT_LLVM_print_uset_impl/,/}/d' \
	  -e '/define void @IsaSAT_LLVM_print_purelit_elim_impl/,/}/d' \
	  -e '/define void @IsaSAT_LLVM_print_purelit_rounds_impl/,/}/d' \
	  -e '/define void @IsaSAT_LLVM_print_binary_red_removed_impl/,/}/d' \
	  -e '/define void @IsaSAT_LLVM_print_binary_red_removed_impl/,/}/d' \
	  -e '/define void @IsaSAT_LLVM_print_lres_impl/,/}/d' \
	  -e '/define void @IsaSAT_LLVM_print_res_impl/,/}/d' \
	  -e '/define void @IsaSAT_LLVM_print_dec_impl/,/}/d' \
	  -e '/define void @IsaSAT_LLVM_print_confl_impl/,/}/d' \
	  -e '/define void @IsaSAT_LLVM_print_propa_impl/,/}/d' \
	  -e '/define void @IsaSAT_Show_LLVM_print_c_impl/,/}/d' \
	  -e '/define void @IsaSAT_Show_LLVM_print_char_impl/,/}/d' \
	  -e '/define void @IsaSAT_Show_LLVM_print_uint64_impl/,/}/d' \
	  -e '/define void @IsaSAT_Show_LLVM_print_open_colour_impl/,/}/d' \
	  -e '/define void @IsaSAT_Show_LLVM_print_close_colour_impl/,/}/d' \
	  -e '/define void @IsaSAT_Profile_LLVM_start_profile/,/}/d' \
	  -e '/define void @IsaSAT_Profile_LLVM_stop_profile/,/}/d' \
	  -e '/define void @IsaSAT_Setup3_LLVM_print_encoded_lit_code/,/}/d' \
	  -e '/define void @IsaSAT_Setup3_LLVM_print_encoded_lit_end_code/,/}/d' \
	  -e '/define void @IsaSAT_Setup3_LLVM_print_literal_of_trail_code/,/}/d' \
	  -e '/define void @IsaSAT_Proofs_LLVM_log_literal_impl/,/}/d' \
	  -e '/define void @IsaSAT_Proofs_LLVM_log_end_clause_impl/,/}/d' \
	  -e '/define void @IsaSAT_Proofs_LLVM_log_start_new_clause_impl/,/}/d' \
	  -e '/define void @IsaSAT_Proofs_LLVM_log_start_del_clause_impl/,/}/d' \
	  -e '/define void @IsaSAT_Proofs_LLVM_mark_literal_for_unit_deletion_impl/,/}/d' \
	  -e '/define void @IsaSAT_Proofs_LLVM_mark_clause_for_unit_as_changed_impl/,/}/d' \
	  -e '/define void @IsaSAT_Proofs_LLVM_mark_clause_for_unit_as_unchanged_impl/,/}/d' \
	  -e 's/declare i8\* @isabelle_llvm_calloc(i64, i64)/declare i8* @isabelle_llvm_calloc(i64, i64)\
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
declare void @IsaSAT_LLVM_print_binary_unit_impl(i64)\
declare void @IsaSAT_LLVM_print_binary_red_removed_impl(i64)\
declare void @IsaSAT_LLVM_print_purelit_elim_impl(i64)\
declare void @IsaSAT_LLVM_print_purelit_rounds_impl(i64)\
declare void @IsaSAT_Profile_LLVM_start_profile(i8)\
declare void @IsaSAT_Profile_LLVM_stop_profile(i8)\
declare void @IsaSAT_Setup3_LLVM_print_encoded_lit_code(i32)\
declare void @IsaSAT_Setup3_LLVM_print_encoded_lit_end_code(i32)\
declare void @IsaSAT_Proofs_LLVM_log_end_clause_impl(i64)\
declare void @IsaSAT_Proofs_LLVM_log_literal_impl(i32)\
declare void @IsaSAT_Proofs_LLVM_log_start_new_clause_impl(i64)\
declare void @IsaSAT_Proofs_LLVM_log_start_del_clause_impl(i64)\
declare void @IsaSAT_Setup3_LLVM_print_literal_of_trail_code(i32)\
declare void @IsaSAT_Proofs_LLVM_mark_literal_for_unit_deletion_impl(i32)\
declare void @IsaSAT_Proofs_LLVM_mark_clause_for_unit_as_changed_impl(i64)\
declare void @IsaSAT_Proofs_LLVM_mark_clause_for_unit_as_unchanged_impl(i64)\
/g' \
	    isasat_restart.ll
	# now due to sepref that array do not alias (we cannot even express that due to seperation logic)
	echo "using noalias"
	sed -i "s|define\(.*\*\) %|define\1 noalias %|g" isasat_restart.ll

isallvm:
	#llvm-as -disable-output isasat_restart.ll
	$(CLANG) $(CFLAGS) -DPRINTSTATS=1 -O3 -flto isasat.c "lib_isabelle_llvm.c"  isasat_restart.ll -o isasat

competition:
	$(CLANG) $(CFLAGS) -DNOOPTIONS=1 -DNOPROFILING -flto -O3 isasat.c "lib_isabelle_llvm.c"  isasat_restart.ll -o isasat

clean:
	rm -rf isasat
debug:
	$(CLANG) -Og -DPRINTSTATS=1 isasat.c "lib_isabelle_llvm.c"  isasat_restart.ll -o isasat
