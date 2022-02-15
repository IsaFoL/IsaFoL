theory IsaSAT_Setup0_LLVM
  imports IsaSAT_Setup IsaSAT_Watch_List_LLVM IsaSAT_Lookup_Conflict_LLVM
    More_Sepref.WB_More_Refinement IsaSAT_Clauses_LLVM LBD_LLVM
    IsaSAT_Options_LLVM IsaSAT_VMTF_Setup_LLVM
    IsaSAT_Arena_Sorting_LLVM
    IsaSAT_Rephase_LLVM
    IsaSAT_EMA_LLVM
    IsaSAT_Stats_LLVM
    IsaSAT_VDom_LLVM
    Isabelle_LLVM.LLVM_DS_Block_Alloc
begin

no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation WB_More_Refinement.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)
hide_const (open) NEMonad.ASSERT NEMonad.RETURN

text \<open>
This is the setup for accessing and modifying the state. The construction is kept generic 
(even if still targetting only our state). There is a lot of copy-paste that would be nice to automate
at some point.


We define 3 sort of operations:

  \<^enum> extracting an element, replacing it by an default element. Modifies the state. The name starts 
with \<^text>\<open>exctr\<close>

  \<^enum> reinserting an element, freeing the current one. Modifies the state. The name starts with
 \<^text>\<open>update\<close>

  \<^enum> in-place reading a value, possibly with pure parameters. Does not modify the state. The name
starts with \<^text>\<open>read\<close>

\<close>
(* setup \<open>map_theory_claset (fn ctxt => ctxt delSWrapper ("split_all_tac"))\<close> *)
term ll_bpto
term ll_load
  term ll_ref
(*TODO Move*)

paragraph \<open>Options\<close>
sepref_register mop_arena_length

(* TODO: Move *)
type_synonym arena_assn = \<open>(32 word, 64) array_list\<close>


type_synonym twl_st_wll_trail_fast =
  \<open>trail_pol_fast_assn \<times> arena_assn \<times> option_lookup_clause_assn \<times>
    64 word \<times> watched_wl_uint32 \<times> vmtf_remove_assn \<times>
    32 word \<times> cach_refinement_l_assn \<times> lbd_assn \<times> out_learned_assn \<times> stats \<times>
    heur_assn \<times>
   aivdom_assn \<times> (64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word) \<times>
  opts_assn \<times> arena_assn\<close>

(* datatype isasat_int = IsaSAT_int
 *   (get_trail_wl_heur: trail_pol_fast_assn)
 *   (get_clauses_wl_heur: arena_assn)
 *   (get_conflict_wl_heur: option_lookup_clause_assn)
 *   (literals_to_update_wl_heur: \<open>64 word\<close>)
 *   (get_watched_wl_heur: \<open>watched_wl_uint32\<close>)
 *   (get_vmtf_heur: vmtf_remove_assn)
 *   (get_count_max_lvls_heur: \<open>32 word\<close>)
 *   (get_conflict_cach: cach_refinement_l_assn)
 *   (get_lbd: lbd_assn)
 *   (get_outlearned_heur: out_learned_assn)
 *   (get_heur: heur_assn)
 *   (get_stats_heur: stats)
 *   (get_aivdom: aivdom_assn)
 *   (get_learned_count: \<open>64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word\<close>)
 *   (get_opts: opts_assn)
 *   (get_old_arena: arena_assn) *)

instantiation isasat_int ::
  (llvm_rep,llvm_rep,llvm_rep,llvm_rep,
  llvm_rep,llvm_rep,llvm_rep,llvm_rep,
  llvm_rep,llvm_rep,llvm_rep,llvm_rep,
  llvm_rep,llvm_rep,llvm_rep,llvm_rep) llvm_rep
begin
  definition to_val_isasat_int where
    \<open>to_val_isasat_int \<equiv> (\<lambda>S. case S of
     IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena \<Rightarrow> LL_STRUCT [to_val M, to_val N, to_val D, to_val i, to_val W, to_val ivmtf,
       to_val icount, to_val ccach, to_val lbd,
       to_val outl, to_val stats, to_val heur, to_val aivdom,  to_val clss, to_val opts, to_val arena])\<close>

  definition from_val_isasat_int :: \<open>llvm_val \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
    \<open>from_val_isasat_int \<equiv> (\<lambda>p. case llvm_val.the_fields p of
   [M, N, D, i, W, ivmtf, icount, ccach, lbd, outl, stats, heur, aivdom, clss, opts, arena] \<Rightarrow>
     IsaSAT_int (from_val M) (from_val N) (from_val D) (from_val i) (from_val W) (from_val ivmtf) (from_val icount) (from_val ccach) (from_val lbd)
       (from_val outl) (from_val stats) (from_val heur) (from_val aivdom) (from_val clss) (from_val opts) (from_val arena))\<close>

  definition [simp]: "struct_of_isasat_int (_ :: ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) isasat_int itself) \<equiv>
     VS_STRUCT [struct_of TYPE('a), struct_of TYPE('b), struct_of TYPE('c),
      struct_of TYPE('d), struct_of TYPE('e), struct_of TYPE('f), struct_of TYPE('g), struct_of TYPE('h),
      struct_of TYPE('i), struct_of TYPE('j), struct_of TYPE('k), struct_of TYPE('l),
      struct_of TYPE('m), struct_of TYPE('n), struct_of TYPE('o), struct_of TYPE('p)]"

  definition [simp]: "init_isasat_int :: ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<equiv> IsaSAT_int init init init init init init init init init init init init init init init init"

  instance
    apply standard
    unfolding from_val_isasat_int_def to_val_isasat_int_def struct_of_isasat_int_def init_isasat_int_def comp_def isasat_int.case_distrib
    subgoal
      by (auto simp: init_zero fun_eq_iff from_val_isasat_int_def split: isasat_int.splits)
    subgoal for v
      by (cases v) (auto split: list.splits isasat_int.splits)
    subgoal for v
      by (cases v)
       (simp add: LLVM_Shallow.null_def to_val_ptr_def split: isasat_int.splits)
    subgoal
      by (simp add: LLVM_Shallow.null_def to_val_ptr_def to_val_word_def init_zero split: isasat_int.splits)
    done
end

subsubsection \<open>Setup for LLVM code export\<close>
text \<open>Declare structure to code generator.\<close>
lemma to_val_isasat_int[ll_to_val]: "to_val x = LL_STRUCT [
  to_val (get_trail_wl_heur x),
  to_val (get_clauses_wl_heur x),
  to_val (get_conflict_wl_heur x),
  to_val (literals_to_update_wl_heur x),
  to_val (get_watched_wl_heur x),
  to_val (get_vmtf_heur x),
  to_val (get_count_max_lvls_heur x),
  to_val (get_conflict_cach x),
  to_val (get_lbd x),
  to_val (get_outlearned_heur x),
  to_val (get_stats_heur x),
  to_val (get_heur x),
  to_val (get_aivdom x),
  to_val (get_learned_count x),
  to_val (get_opts x),
  to_val (get_old_arena x)]"
  apply (cases x)
  apply (auto simp: to_val_isasat_int_def)
  done

lemma node_insert_value:
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) M' 0 = Mreturn (IsaSAT_int M' N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) N' (Suc 0) = Mreturn (IsaSAT_int M N' D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) D' 2 = Mreturn (IsaSAT_int M N D' i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) i' 3 = Mreturn (IsaSAT_int M N D i' W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) W' 4 = Mreturn (IsaSAT_int M N D i W' ivmtf icount ccach lbd outl stats heur aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) ivmtf' 5 = Mreturn (IsaSAT_int M N D i W ivmtf' icount ccach lbd outl stats heur aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) icount' 6 = Mreturn (IsaSAT_int M N D i W ivmtf icount' ccach lbd outl stats heur aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) ccach' 7 = Mreturn (IsaSAT_int M N D i W ivmtf icount ccach' lbd outl stats heur aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) lbd' 8 = Mreturn (IsaSAT_int M N D i W ivmtf icount ccach lbd' outl stats heur aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) outl' 9 = Mreturn (IsaSAT_int M N D i W ivmtf icount ccach lbd outl' stats heur aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) stats' 10 = Mreturn (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats' heur aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) heur' 11 = Mreturn (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur' aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) aivdom' 12 = Mreturn (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom' clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) clss' 13 = Mreturn (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss' opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) opts' 14 = Mreturn (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts' arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) arena' 15 = Mreturn (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena')"
  by (simp_all add: ll_insert_value_def llvm_insert_value_def Let_def checked_from_val_def
                to_val_isasat_int_def from_val_isasat_int_def)

lemma node_extract_value:
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) 0 = Mreturn M"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) (Suc 0) = Mreturn N"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) 2 = Mreturn D"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) 3 = Mreturn i"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) 4 = Mreturn W"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) 5 = Mreturn ivmtf"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) 6 = Mreturn icount"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) 7 = Mreturn ccach"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) 8 = Mreturn lbd"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) 9 = Mreturn outl"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) 10 = Mreturn stats"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) 11 = Mreturn heur"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) 12 = Mreturn aivdom"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) 13 = Mreturn clss"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) 14 = Mreturn opts"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena) 15 = Mreturn arena"
  apply (simp_all add: ll_extract_value_def llvm_extract_value_def Let_def checked_from_val_def
                to_val_isasat_int_def from_val_isasat_int_def)
  done

text \<open>Lemmas to translate node construction and destruction\<close>
lemma inline_return_node[llvm_pre_simp]: "Mreturn (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) = doM {
    r \<leftarrow> ll_insert_value init M 0;
    r \<leftarrow> ll_insert_value r N 1;
    r \<leftarrow> ll_insert_value r D 2;
    r \<leftarrow> ll_insert_value r i 3;
    r \<leftarrow> ll_insert_value r W 4;
    r \<leftarrow> ll_insert_value r ivmtf 5;
    r \<leftarrow> ll_insert_value r icount 6;
    r \<leftarrow> ll_insert_value r ccach 7;
    r \<leftarrow> ll_insert_value r lbd 8;
    r \<leftarrow> ll_insert_value r outl 9;
    r \<leftarrow> ll_insert_value r heur 10;
    r \<leftarrow> ll_insert_value r stats 11;
    r \<leftarrow> ll_insert_value r aivdom 12;
    r \<leftarrow> ll_insert_value r clss 13;
    r \<leftarrow> ll_insert_value r opts 14;
    r \<leftarrow> ll_insert_value r arena 15;
    Mreturn r
  }"
  apply (auto simp: node_insert_value)
  done

lemma inline_node_case[llvm_pre_simp]: "(case r of (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) \<Rightarrow> f M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) = doM {
    M \<leftarrow> ll_extract_value r 0;
    N \<leftarrow> ll_extract_value r 1;
    D \<leftarrow> ll_extract_value r 2;
    i \<leftarrow> ll_extract_value r 3;
    W \<leftarrow> ll_extract_value r 4;
    ivmtf \<leftarrow> ll_extract_value r 5;
    icount \<leftarrow> ll_extract_value r 6;
    ccach \<leftarrow> ll_extract_value r 7;
    lbd \<leftarrow> ll_extract_value r 8;
    outl \<leftarrow> ll_extract_value r 9;
    heur \<leftarrow> ll_extract_value r 10;
    stats \<leftarrow> ll_extract_value r 11;
    aivdom \<leftarrow> ll_extract_value r 12;
    clss \<leftarrow> ll_extract_value r 13;
    opts \<leftarrow> ll_extract_value r 14;
    arena \<leftarrow> ll_extract_value r 15;
  f M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena
}"
  apply (cases r)
  apply (auto simp: node_extract_value)
  done

lemma inline_return_node_case[llvm_pre_simp]: "doM {Mreturn (case r of (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) \<Rightarrow> f M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)} = doM {
    M \<leftarrow> ll_extract_value r 0;
    N \<leftarrow> ll_extract_value r 1;
    D \<leftarrow> ll_extract_value r 2;
    i \<leftarrow> ll_extract_value r 3;
    W \<leftarrow> ll_extract_value r 4;
    ivmtf \<leftarrow> ll_extract_value r 5;
    icount \<leftarrow> ll_extract_value r 6;
    ccach \<leftarrow> ll_extract_value r 7;
    lbd \<leftarrow> ll_extract_value r 8;
    outl \<leftarrow> ll_extract_value r 9;
    heur \<leftarrow> ll_extract_value r 10;
    stats \<leftarrow> ll_extract_value r 11;
    aivdom \<leftarrow> ll_extract_value r 12;
    clss \<leftarrow> ll_extract_value r 13;
    opts \<leftarrow> ll_extract_value r 14;
    arena \<leftarrow> ll_extract_value r 15;
  Mreturn (f M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)
}"
  apply (cases r)
  apply (auto simp: node_extract_value)
  done
lemma inline_direct_return_node_case[llvm_pre_simp]: "doM {(case r of (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) \<Rightarrow> f M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)} = doM {
    M \<leftarrow> ll_extract_value r 0;
    N \<leftarrow> ll_extract_value r 1;
    D \<leftarrow> ll_extract_value r 2;
    i \<leftarrow> ll_extract_value r 3;
    W \<leftarrow> ll_extract_value r 4;
    ivmtf \<leftarrow> ll_extract_value r 5;
    icount \<leftarrow> ll_extract_value r 6;
    ccach \<leftarrow> ll_extract_value r 7;
    lbd \<leftarrow> ll_extract_value r 8;
    outl \<leftarrow> ll_extract_value r 9;
    heur \<leftarrow> ll_extract_value r 10;
    stats \<leftarrow> ll_extract_value r 11;
    aivdom \<leftarrow> ll_extract_value r 12;
    clss \<leftarrow> ll_extract_value r 13;
    opts \<leftarrow> ll_extract_value r 14;
    arena \<leftarrow> ll_extract_value r 15;
   (f M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)
}"
  apply (cases r)
  apply (auto simp: node_extract_value)
  done

lemmas [llvm_inline] =
  isasat_int.get_trail_wl_heur_def
  isasat_int.get_clauses_wl_heur_def
  isasat_int.get_conflict_wl_heur_def
  isasat_int.literals_to_update_wl_heur_def
  isasat_int.get_watched_wl_heur_def
  isasat_int.get_vmtf_heur_def
  isasat_int.get_count_max_lvls_heur_def
  isasat_int.get_conflict_cach_def
  isasat_int.get_lbd_def
  isasat_int.get_outlearned_heur_def
  isasat_int.get_heur_def
  isasat_int.get_stats_heur_def
  isasat_int.get_aivdom_def
  isasat_int.get_learned_count_def
  isasat_int.get_opts_def
  isasat_int.get_old_arena_def

fun isasat_int_assn :: \<open>
  ('a \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow>
  ('b \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow>
  ('c \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow>
  ('d \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow>
  ('e \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow>
  ('f \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow>
  ('g \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow>
  ('h \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow>
  ('i \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow>
  ('j \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow>
  ('k \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow>
  ('l \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow>
  ('m \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow>
  ('n \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow>
  ('o \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow>
  ('p \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow>
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>isasat_int_assn a_assn b_assn' c_assn d_assn e_assn f_assn g_assn h_assn i_assn j_assn k_assn l_assn m_assn n_assn o_assn p_assn S T =
   (case (S, T) of
  (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena,
   IsaSAT_int M' N' D' i' W' ivmtf' icount' ccach' lbd' outl' heur' stats' aivdom' clss' opts' arena')
     \<Rightarrow>
 (a_assn M (M') \<and>* b_assn' N (N') \<and>* c_assn D (D')  \<and>* d_assn i (i') \<and>*
 e_assn W (W') \<and>* f_assn ivmtf (ivmtf') \<and>* g_assn icount (icount')  \<and>* h_assn ccach (ccach') \<and>*
 i_assn lbd (lbd') \<and>* j_assn outl (outl') \<and>* k_assn heur (heur')  \<and>* l_assn stats (stats') \<and>*
 m_assn aivdom (aivdom') \<and>* n_assn clss (clss') \<and>* o_assn opts (opts')  \<and>* p_assn arena (arena')))
  \<close>

type_synonym twl_st_wll_trail_fast2 =
  \<open>(trail_pol_fast_assn, arena_assn, option_lookup_clause_assn,
    64 word, watched_wl_uint32, vmtf_remove_assn,
    32 word, cach_refinement_l_assn, lbd_assn, out_learned_assn, 
    stats, heur_assn,
   aivdom_assn, (64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word),
  opts_assn, arena_assn) isasat_int\<close>
definition isasat_bounded_assn :: \<open>isasat \<Rightarrow> twl_st_wll_trail_fast2 \<Rightarrow> assn\<close> where
\<open>isasat_bounded_assn = isasat_int_assn
  trail_pol_fast_assn  arena_fast_assn
  conflict_option_rel_assn
  sint64_nat_assn
  watchlist_fast_assn
  vmtf_remove_assn
  uint32_nat_assn
  cach_refinement_l_assn
  lbd_assn
  out_learned_assn
  stats_assn
  heuristic_assn
  aivdom_assn
  lcount_assn
  opts_assn  arena_fast_assn\<close>

lemma [sepref_fr_rules]: \<open>(Mreturn o isasat_int.literals_to_update_wl_heur, RETURN o isasat_int.literals_to_update_wl_heur) \<in> isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  supply [split] =  isasat_int.splits
  unfolding isasat_bounded_assn_def
  apply sepref_to_hoare
  apply (vcg')
  done


locale isasat_state_ops =
  fixes
    a_assn :: \<open>'a \<Rightarrow> 'xa \<Rightarrow> assn\<close> and
    b_assn :: \<open>'b \<Rightarrow> 'xb \<Rightarrow> assn\<close> and
    c_assn :: \<open>'c \<Rightarrow> 'xc \<Rightarrow> assn\<close> and
    d_assn :: \<open>'d \<Rightarrow> 'xd \<Rightarrow> assn\<close> and
    e_assn :: \<open>'e \<Rightarrow> 'xe \<Rightarrow> assn\<close> and
    f_assn :: \<open>'f \<Rightarrow> 'xf \<Rightarrow> assn\<close> and
    g_assn :: \<open>'g \<Rightarrow> 'xg \<Rightarrow> assn\<close> and
    h_assn :: \<open>'h \<Rightarrow> 'xh \<Rightarrow> assn\<close> and
    i_assn :: \<open>'i \<Rightarrow> 'xi \<Rightarrow> assn\<close> and
    j_assn :: \<open>'j \<Rightarrow> 'xj \<Rightarrow> assn\<close> and
    k_assn :: \<open>'k \<Rightarrow> 'xk \<Rightarrow> assn\<close> and
    l_assn :: \<open>'l \<Rightarrow> 'xl \<Rightarrow> assn\<close> and
    m_assn :: \<open>'m \<Rightarrow> 'xm \<Rightarrow> assn\<close> and
    n_assn :: \<open>'n \<Rightarrow> 'xn \<Rightarrow> assn\<close> and
    o_assn :: \<open>'o \<Rightarrow> 'xo \<Rightarrow> assn\<close> and
    p_assn :: \<open>'p \<Rightarrow> 'xp \<Rightarrow> assn\<close> and
    a_default :: 'a and
    a :: \<open>'xa llM\<close> and
    b_default :: 'b and
    b :: \<open>'xb llM\<close> and
    c_default :: 'c and
    c :: \<open>'xc llM\<close> and
    d_default :: 'd and
    d :: \<open>'xd llM\<close> and
    e_default :: 'e and
    e :: \<open>'xe llM\<close> and
    f_default :: 'f and
    f :: \<open>'xf llM\<close> and
    g_default :: 'g and
    g :: \<open>'xg llM\<close> and
    h_default :: 'h and
    h :: \<open>'xh llM\<close> and
    i_default :: 'i and
    i :: \<open>'xi llM\<close> and
    j_default :: 'j and
    j :: \<open>'xj llM\<close> and
    k_default :: 'k and
    k :: \<open>'xk llM\<close> and
    l_default :: 'l and
    l :: \<open>'xl llM\<close> and
    m_default :: 'm and
    m :: \<open>'xm llM\<close> and
    n_default :: 'n and
    n :: \<open>'xn llM\<close> and
    ko_default :: 'o and
    ko :: \<open>'xo llM\<close> and
    p_default :: 'p and
    p :: \<open>'xp llM\<close>
begin

definition isasat_assn :: \<open>_ \<Rightarrow> _ \<Rightarrow> assn\<close> where
\<open>isasat_assn = isasat_int_assn
  a_assn b_assn c_assn d_assn
  e_assn f_assn g_assn h_assn
  i_assn j_assn k_assn l_assn
  m_assn n_assn o_assn p_assn\<close>

definition remove_trail_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _ \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_trail_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x1, IsaSAT_int a_default x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16))\<close>

definition remove_arena_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'b \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_arena_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x2, IsaSAT_int x1 b_default x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16))\<close>

definition remove_conflict_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _ \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_conflict_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x3, IsaSAT_int x1 x2 c_default x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16))\<close>

definition remove_literals_to_update_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _ \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_literals_to_update_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x4, IsaSAT_int x1 x2 x3 d_default x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16))\<close>

definition remove_watchlist_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'e \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_watchlist_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x5, IsaSAT_int x1 x2 x3 x4 e_default x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16))\<close>

definition remove_vmtf_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'f \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_vmtf_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x6, IsaSAT_int x1 x2 x3 x4 x5 f_default x7 x8 x9 x10 x11 x12 x13 x14 x15 x16))\<close>

definition remove_clvls_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'g \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_clvls_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x7, IsaSAT_int x1 x2 x3 x4 x5 x6 g_default x8 x9 x10 x11 x12 x13 x14 x15 x16))\<close>

definition remove_ccach_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'h \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_ccach_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x8, IsaSAT_int x1 x2 x3 x4 x5 x6 x7 h_default x9 x10 x11 x12 x13 x14 x15 x16))\<close>

definition remove_lbd_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'i \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_lbd_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x9, IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 i_default x10 x11 x12 x13 x14 x15 x16))\<close>

definition remove_outl_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'j \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_outl_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x10, IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 j_default x11 x12 x13 x14 x15 x16))\<close>

definition remove_stats_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'k \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_stats_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x11, IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 k_default x12 x13 x14 x15 x16))\<close>

definition remove_heur_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'l \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_heur_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x12, IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 l_default x13 x14 x15 x16))\<close>

definition remove_vdom_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'm \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_vdom_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x13, IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 m_default x14 x15 x16))\<close>

definition remove_lcount_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'n \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_lcount_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x14, IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 n_default x15 x16))\<close>

definition remove_opts_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'o \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_opts_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x15, IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ko_default x16))\<close>

definition remove_old_arena_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'p \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_old_arena_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x16, IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 p_default))\<close>

definition update_trail_wl_heur :: \<open>'a \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>update_trail_wl_heur x1 isasat_int = (case isasat_int of IsaSAT_int M x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
    let _ = M in
    IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16)\<close>

definition update_arena_wl_heur :: \<open>'b \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>update_arena_wl_heur x2 isasat_int = (case isasat_int of IsaSAT_int x1 M x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
    let _ = M in
    IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16)\<close>

definition update_conflict_wl_heur :: \<open>'c \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>update_conflict_wl_heur x3 isasat_int = (case isasat_int of IsaSAT_int x1 x2 M x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
    let _ = M in
    IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16)\<close>

definition update_literals_to_update_wl_heur :: \<open>'d \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>update_literals_to_update_wl_heur x4 isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 M x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
    let _ = M in
    IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16)\<close>

definition update_watchlist_wl_heur :: \<open>'e \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>update_watchlist_wl_heur x5 isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 M x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
    let _ = M in
    IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16)\<close>

definition update_vmtf_wl_heur :: \<open>'f \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>update_vmtf_wl_heur x6 isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 M x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
    let _ = M in
    IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16)\<close>

definition update_clvls_wl_heur :: \<open>'g \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>update_clvls_wl_heur x7 isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 M x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
    let _ = M in
    IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16)\<close>

definition update_ccach_wl_heur :: \<open>'h \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>update_ccach_wl_heur x8 isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 M x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
    let _ = M in
    IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16)\<close>

definition update_lbd_wl_heur :: \<open>'i \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>update_lbd_wl_heur x9 isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 M x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
    let _ = M in
    IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16)\<close>

definition update_outl_wl_heur :: \<open>'j \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>update_outl_wl_heur x10 isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 M x11 x12 x13 x14 x15 x16 \<Rightarrow>
    let _ = M in
    IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16)\<close>

definition update_stats_wl_heur :: \<open>'k \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>update_stats_wl_heur x11 isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 M x12 x13 x14 x15 x16 \<Rightarrow>
    let _ = M in
    IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16)\<close>

definition update_heur_wl_heur :: \<open>'l \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>update_heur_wl_heur x12 isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 M x13 x14 x15 x16 \<Rightarrow>
    let _ = M in
    IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16)\<close>

definition update_vdom_wl_heur :: \<open>'m \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>update_vdom_wl_heur x13 isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 M x14 x15 x16 \<Rightarrow>
    let _ = M in
    IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16)\<close>

definition update_lcount_wl_heur :: \<open>'n \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>update_lcount_wl_heur x14 isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 M x15 x16 \<Rightarrow>
    let _ = M in
    IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16)\<close>

definition update_opts_wl_heur :: \<open>'o \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>update_opts_wl_heur x15 isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 M x16 \<Rightarrow>
    let _ = M in
    IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16)\<close>


definition update_old_arena_wl_heur :: \<open>'p \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>update_old_arena_wl_heur x16 isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 M \<Rightarrow>
    let _ = M in
    IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16)\<close>


end
 
lemma isasat_int_assn_conv[simp]: 
  "isasat_int_assn P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 (IsaSAT_int a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16)
  (IsaSAT_int a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15' a16') =
  (P1 a1 a1' \<and>*
  P2 a2 a2' \<and>*
  P3 a3 a3' \<and>*
  P4 a4 a4' \<and>*
  P5 a5 a5' \<and>*
  P6 a6 a6' \<and>*
  P7 a7 a7' \<and>*
  P8 a8 a8' \<and>* P9 a9 a9' \<and>* P10 a10 a10' \<and>* P11 a11 a11' \<and>* P12 a12 a12' \<and>* P13 a13 a13' \<and>* P14 a14 a14' \<and>* P15 a15 a15' \<and>* P16 a16 a16')"
  unfolding isasat_int_assn.simps by auto
lemma isasat_int_assn_ctxt:
  \<open>isasat_int_assn P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 (IsaSAT_int a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16)
  (IsaSAT_int a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15' a16') = z \<Longrightarrow>
  hn_ctxt (isasat_int_assn P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16) (IsaSAT_int a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16)
  (IsaSAT_int a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15' a16')= z\<close>
  by (simp add: hn_ctxt_def)

lemma hn_case_isasat_int'[sepref_comb_rules]:
  assumes FR: \<open>\<Gamma> \<turnstile> hn_ctxt (isasat_int_assn P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16) p' p ** \<Gamma>1\<close>
  assumes Pair: "\<And>a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15' a16'.
        \<lbrakk>p'=IsaSAT_int a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15' a16'\<rbrakk>
    \<Longrightarrow> hn_refine (hn_ctxt P1 a1' a1 \<and>* hn_ctxt P2 a2' a2 \<and>* hn_ctxt P3 a3' a3 \<and>* hn_ctxt P4 a4' a4 \<and>*
       hn_ctxt P5 a5' a5 \<and>* hn_ctxt P6 a6' a6 \<and>* hn_ctxt P7 a7' a7 \<and>* hn_ctxt P8 a8' a8 \<and>*
       hn_ctxt P9 a9' a9 \<and>* hn_ctxt P10 a10' a10 \<and>* hn_ctxt P11 a11' a11 \<and>* hn_ctxt P12 a12' a12 \<and>*
       hn_ctxt P13 a13' a13 \<and>* hn_ctxt P14 a14' a14 \<and>* hn_ctxt P15 a15' a15 \<and>* hn_ctxt P16 a16' a16 \<and>* \<Gamma>1)
          (f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16)
          (\<Gamma>2 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15' a16') R
          (CP a1 a2  a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16)
         (f' a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15' a16')"
  assumes FR2: \<open>\<And>a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15' a16'.
       \<Gamma>2 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15' a16' \<turnstile>
       hn_ctxt P1' a1' a1 ** hn_ctxt P2' a2' a2 ** hn_ctxt P3' a3' a3 ** hn_ctxt P4' a4' a4 **
       hn_ctxt P5' a5' a5 ** hn_ctxt P6' a6' a6 ** hn_ctxt P7' a7' a7 ** hn_ctxt P8' a8' a8 **
       hn_ctxt P9' a9' a9 ** hn_ctxt P10' a10' a10 ** hn_ctxt P11' a11' a11 ** hn_ctxt P12' a12' a12 **
       hn_ctxt P13' a13' a13 ** hn_ctxt P14' a14' a14 ** hn_ctxt P15' a15' a15 ** hn_ctxt P16' a16' a16 ** \<Gamma>1'\<close>
  shows \<open>hn_refine \<Gamma> (case_isasat_int f p) (hn_ctxt (isasat_int_assn P1' P2' P3' P4' P5' P6' P7' P8' P9' P10' P11' P12' P13' P14' P15' P16') p' p ** \<Gamma>1')
    R (case_isasat_int CP p) (case_isasat_int$(\<lambda>\<^sub>2a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16. f' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16)$p')\<close> (is \<open>?G \<Gamma>\<close>)
  unfolding autoref_tag_defs PROTECT2_def
  apply1 (rule hn_refine_cons_pre[OF FR])
    apply1 (cases p; cases p'; simp add: isasat_int_assn_conv[THEN isasat_int_assn_ctxt])
  unfolding CP_SPLIT_def prod.simps
  apply (rule hn_refine_cons[OF _ Pair _ entails_refl])
  applyS (simp add: hn_ctxt_def)
  applyS simp using FR2
  by (simp add: hn_ctxt_def)


lemma case_isasat_int_arity[sepref_monadify_arity]:
  \<open>case_isasat_int \<equiv> \<lambda>\<^sub>2fp p. SP case_isasat_int$(\<lambda>\<^sub>2a b. fp$a$b)$p\<close>
  by (simp_all only: SP_def APP_def PROTECT2_def RCALL_def)

lemma case_isasat_int_comb[sepref_monadify_comb]:
  \<open>\<And>fp p. case_isasat_int$fp$p \<equiv> Refine_Basic.bind$(EVAL$p)$(\<lambda>\<^sub>2p. (SP case_isasat_int$fp$p))\<close>
  by (simp_all)

lemma case_isasat_int_plain_comb[sepref_monadify_comb]:
  "EVAL$(case_isasat_int$(\<lambda>\<^sub>2a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16. fp a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16)$p) \<equiv>
    Refine_Basic.bind$(EVAL$p)$(\<lambda>\<^sub>2p. case_isasat_int$(\<lambda>\<^sub>2a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16. EVAL$(fp a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16))$p)"
  apply (rule eq_reflection, simp split: list.split prod.split option.split isasat_int.split)+
  done

lemma ho_isasat_int_move[sepref_preproc]: \<open>case_isasat_int (\<lambda>a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 x. f x a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16) =
  (\<lambda>p x. case_isasat_int (f x) p)\<close>
  by (auto split: isasat_int.splits)

locale isasat_state =
  isasat_state_ops a_assn b_assn c_assn d_assn e_assn
  f_assn g_assn h_assn i_assn j_assn
  k_assn l_assn m_assn n_assn o_assn p_assn
  a_default a
  b_default b
  c_default c
  d_default d
  e_default e
  f_default f
  g_default g
  h_default h
  i_default i
  j_default j
  k_default k
  l_default l
  m_default m
  n_default n
  ko_default ko
  p_default p
  for
    a_assn :: \<open>'a \<Rightarrow> 'xa \<Rightarrow> assn\<close> and
    b_assn :: \<open>'b \<Rightarrow> 'xb \<Rightarrow> assn\<close> and
    c_assn :: \<open>'c \<Rightarrow> 'xc \<Rightarrow> assn\<close> and
    d_assn :: \<open>'d \<Rightarrow> 'xd \<Rightarrow> assn\<close> and
    e_assn :: \<open>'e \<Rightarrow> 'xe \<Rightarrow> assn\<close> and
    f_assn :: \<open>'f \<Rightarrow> 'xf \<Rightarrow> assn\<close> and
    g_assn :: \<open>'g \<Rightarrow> 'xg \<Rightarrow> assn\<close> and
    h_assn :: \<open>'h \<Rightarrow> 'xh \<Rightarrow> assn\<close> and
    i_assn :: \<open>'i \<Rightarrow> 'xi \<Rightarrow> assn\<close> and
    j_assn :: \<open>'j \<Rightarrow> 'xj \<Rightarrow> assn\<close> and
    k_assn :: \<open>'k \<Rightarrow> 'xk \<Rightarrow> assn\<close> and
    l_assn :: \<open>'l \<Rightarrow> 'xl \<Rightarrow> assn\<close> and
    m_assn :: \<open>'m \<Rightarrow> 'xm \<Rightarrow> assn\<close> and
    n_assn :: \<open>'n \<Rightarrow> 'xn \<Rightarrow> assn\<close> and
    o_assn :: \<open>'o \<Rightarrow> 'xo \<Rightarrow> assn\<close> and
    p_assn :: \<open>'p \<Rightarrow> 'xp \<Rightarrow> assn\<close> and
    a_default :: 'a and
    a :: \<open>'xa llM\<close> and
    b_default :: 'b and
    b :: \<open>'xb llM\<close> and
    c_default :: 'c and
    c :: \<open>'xc llM\<close> and
    d_default :: 'd and
    d :: \<open>'xd llM\<close> and
    e_default :: 'e and
    e :: \<open>'xe llM\<close> and
    f_default :: 'f and
    f :: \<open>'xf llM\<close> and
    g_default :: 'g and
    g :: \<open>'xg llM\<close> and
    h_default :: 'h and
    h :: \<open>'xh llM\<close> and
    i_default :: 'i and
    i :: \<open>'xi llM\<close> and
    j_default :: 'j and
    j :: \<open>'xj llM\<close> and
    k_default :: 'k and
    k :: \<open>'xk llM\<close> and
    l_default :: 'l and
    l :: \<open>'xl llM\<close> and
    m_default :: 'm and
    m :: \<open>'xm llM\<close> and
    n_default :: 'n and
    n :: \<open>'xn llM\<close> and
    ko_default :: 'o and
    ko :: \<open>'xo llM\<close> and
    p_default :: 'p and
    p :: \<open>'xp llM\<close> and
    a_free :: \<open>'xa \<Rightarrow> unit llM\<close> and
    b_free :: \<open>'xb \<Rightarrow> unit llM\<close> and
    c_free :: \<open>'xc \<Rightarrow> unit llM\<close> and
    d_free :: \<open>'xd \<Rightarrow> unit llM\<close> and
    e_free :: \<open>'xe \<Rightarrow> unit llM\<close> and
    f_free :: \<open>'xf \<Rightarrow> unit llM\<close> and
    g_free :: \<open>'xg \<Rightarrow> unit llM\<close> and
    h_free :: \<open>'xh \<Rightarrow> unit llM\<close> and
    i_free :: \<open>'xi \<Rightarrow> unit llM\<close> and
    j_free :: \<open>'xj \<Rightarrow> unit llM\<close> and
    k_free :: \<open>'xk \<Rightarrow> unit llM\<close> and
    l_free :: \<open>'xl \<Rightarrow> unit llM\<close> and
    m_free :: \<open>'xm \<Rightarrow> unit llM\<close> and
    n_free :: \<open>'xn \<Rightarrow> unit llM\<close> and
    o_free :: \<open>'xo \<Rightarrow> unit llM\<close> and
    p_free :: \<open>'xp \<Rightarrow> unit llM\<close> +
  assumes
    a: \<open>(uncurry0 a, uncurry0  (RETURN a_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a a_assn\<close> and
    b: \<open>(uncurry0 b, uncurry0  (RETURN b_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a b_assn\<close> and
    c: \<open>(uncurry0 c, uncurry0  (RETURN c_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a c_assn\<close> and
    d: \<open>(uncurry0 d, uncurry0  (RETURN d_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a d_assn\<close> and
    e: \<open>(uncurry0 e, uncurry0  (RETURN e_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a e_assn\<close> and
    f: \<open>(uncurry0 f, uncurry0  (RETURN f_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a f_assn\<close> and
    g: \<open>(uncurry0 g, uncurry0  (RETURN g_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a g_assn\<close> and
    h: \<open>(uncurry0 h, uncurry0  (RETURN h_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a h_assn\<close> and
    i: \<open>(uncurry0 i, uncurry0  (RETURN i_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a i_assn\<close> and
    j: \<open>(uncurry0 j, uncurry0  (RETURN j_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a j_assn\<close> and
    k: \<open>(uncurry0 k, uncurry0  (RETURN k_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a k_assn\<close> and
    l: \<open>(uncurry0 l, uncurry0  (RETURN l_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a l_assn\<close> and
    m: \<open>(uncurry0 m, uncurry0  (RETURN m_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a m_assn\<close> and
    n: \<open>(uncurry0 n, uncurry0  (RETURN n_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a n_assn\<close> and
    o: \<open>(uncurry0 ko, uncurry0  (RETURN ko_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a o_assn\<close>and
    p: \<open>(uncurry0 p, uncurry0 (RETURN p_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a p_assn\<close> and
    a_free: \<open>MK_FREE a_assn a_free\<close> and
    b_free: \<open>MK_FREE b_assn b_free\<close>and
    c_free: \<open>MK_FREE c_assn c_free\<close>and
    d_free: \<open>MK_FREE d_assn d_free\<close>and
    e_free: \<open>MK_FREE e_assn e_free\<close>and
    f_free: \<open>MK_FREE f_assn f_free\<close>and
    g_free: \<open>MK_FREE g_assn g_free\<close>and
    h_free: \<open>MK_FREE h_assn h_free\<close>and
    i_free: \<open>MK_FREE i_assn i_free\<close>and
    j_free: \<open>MK_FREE j_assn j_free\<close>and
    k_free: \<open>MK_FREE k_assn k_free\<close>and
    l_free: \<open>MK_FREE l_assn l_free\<close>and
    m_free: \<open>MK_FREE m_assn m_free\<close>and
    n_free: \<open>MK_FREE n_assn n_free\<close>and
    o_free: \<open>MK_FREE o_assn o_free\<close>and
    p_free: \<open>MK_FREE p_assn p_free\<close>
  notes [[sepref_register_adhoc a_default b_default c_default d_default e_default f_default g_default h_default
  i_default j_default k_default l_default m_default n_default ko_default p_default]]
begin

lemmas [sepref_comb_rules] = hn_case_isasat_int'[of _ a_assn b_assn c_assn d_assn e_assn f_assn
  g_assn h_assn i_assn j_assn k_assn l_assn m_assn n_assn o_assn p_assn,
  unfolded isasat_assn_def[symmetric]]

lemma ex_isasat_int_iff: "(\<exists>b :: (_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_)isasat_int. P b) \<longleftrightarrow>
  (\<exists>a b  c d e f g h i j k l m n ko p. P (IsaSAT_int a b  c d e f g h i j k l m n ko p))"
  apply auto
    apply (case_tac b)
  by force

lemmas [sepref_frame_free_rules] = a_free b_free c_free d_free e_free f_free g_free h_free i_free
  j_free k_free l_free m_free n_free o_free p_free
sepref_register
  \<open>IsaSAT_int\<close>
lemma [sepref_fr_rules]: \<open>(uncurry15 (Mreturn o\<^sub>1\<^sub>6 IsaSAT_int), uncurry15 (RETURN o\<^sub>1\<^sub>6 IsaSAT_int))
  \<in> a_assn\<^sup>d *\<^sub>a b_assn\<^sup>d *\<^sub>a c_assn\<^sup>d *\<^sub>a d_assn\<^sup>d *\<^sub>a
  e_assn\<^sup>d *\<^sub>a f_assn\<^sup>d *\<^sub>a g_assn\<^sup>d *\<^sub>a h_assn\<^sup>d *\<^sub>a
  i_assn\<^sup>d *\<^sub>a j_assn\<^sup>d *\<^sub>a k_assn\<^sup>d *\<^sub>a l_assn\<^sup>d *\<^sub>a
  m_assn\<^sup>d *\<^sub>a n_assn\<^sup>d *\<^sub>a o_assn\<^sup>d *\<^sub>a p_assn\<^sup>d
  \<rightarrow>\<^sub>a isasat_assn\<close>
  unfolding isasat_assn_def
  apply sepref_to_hoare
  apply vcg
  unfolding ex_isasat_int_iff
  apply vcg'
  done

lemma [sepref_frame_match_rules]:
  \<open> hn_ctxt
     (isasat_int_assn (invalid_assn a_assn) (invalid_assn b_assn) (invalid_assn c_assn) (invalid_assn d_assn) (invalid_assn e_assn)
    (invalid_assn f_assn) (invalid_assn g_assn) (invalid_assn h_assn) (invalid_assn i_assn) (invalid_assn j_assn) (invalid_assn k_assn)
   (invalid_assn l_assn) (invalid_assn m_assn) (invalid_assn n_assn) (invalid_assn o_assn) (invalid_assn p_assn)) ax bx \<turnstile> hn_val UNIV ax bx\<close>
    unfolding hn_ctxt_def invalid_assn_def isasat_assn_def entails_def
    apply (auto split: prod.split isasat_int.splits elim: is_pureE 
      simp: sep_algebra_simps pure_part_pure_conj_eq)
    apply (auto simp: pure_part_def)
      apply (auto simp: pure_def pure_true_conv)
    done

lemma RETURN_case_isasat_int_inverse: \<open>RETURN
      (let _ = M
         in ff) =
      (do {_ \<leftarrow> mop_free M;
         RETURN (ff)})\<close>
    by (auto intro!: ext simp: mop_free_def split: isasat_int.splits)

sepref_def update_trail_wl_heur_code
  is \<open>uncurry (RETURN oo update_trail_wl_heur)\<close>
  :: \<open>a_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=5]]
  unfolding update_trail_wl_heur_def isasat_int.case_distrib comp_def RETURN_case_isasat_int_inverse
  by sepref

sepref_def update_arena_wl_heur_code
  is \<open>uncurry (RETURN oo update_arena_wl_heur)\<close>
  :: \<open>b_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_arena_wl_heur_def isasat_int.case_distrib comp_def RETURN_case_isasat_int_inverse
  by sepref

sepref_def update_conflict_wl_heur_code
  is \<open>uncurry (RETURN oo update_conflict_wl_heur)\<close>
  :: \<open>c_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_conflict_wl_heur_def isasat_int.case_distrib comp_def RETURN_case_isasat_int_inverse
  by sepref

sepref_def update_literals_to_update_wl_heur_code
  is \<open>uncurry (RETURN oo update_literals_to_update_wl_heur)\<close>
  :: \<open>d_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_literals_to_update_wl_heur_def isasat_int.case_distrib comp_def RETURN_case_isasat_int_inverse
  by sepref

sepref_def update_watchlist_wl_heur_code
  is \<open>uncurry (RETURN oo update_watchlist_wl_heur)\<close>
  :: \<open>e_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_watchlist_wl_heur_def isasat_int.case_distrib comp_def RETURN_case_isasat_int_inverse
  by sepref

sepref_def update_vmtf_wl_heur_code
  is \<open>uncurry (RETURN oo update_vmtf_wl_heur)\<close>
  :: \<open>f_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_vmtf_wl_heur_def isasat_int.case_distrib comp_def RETURN_case_isasat_int_inverse
  by sepref

sepref_def update_clvls_wl_heur_code
  is \<open>uncurry (RETURN oo update_clvls_wl_heur)\<close>
  :: \<open>g_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_clvls_wl_heur_def isasat_int.case_distrib comp_def RETURN_case_isasat_int_inverse
  by sepref

sepref_def update_ccach_wl_heur_code
  is \<open>uncurry (RETURN oo update_ccach_wl_heur)\<close>
  :: \<open>h_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_ccach_wl_heur_def isasat_int.case_distrib comp_def RETURN_case_isasat_int_inverse
  by sepref

sepref_def update_lbd_wl_heur_code
  is \<open>uncurry (RETURN oo update_lbd_wl_heur)\<close>
  :: \<open>i_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_lbd_wl_heur_def isasat_int.case_distrib comp_def RETURN_case_isasat_int_inverse
  by sepref

sepref_def update_outl_wl_heur_code
  is \<open>uncurry (RETURN oo update_outl_wl_heur)\<close>
  :: \<open>j_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_outl_wl_heur_def isasat_int.case_distrib comp_def RETURN_case_isasat_int_inverse
  by sepref

sepref_def update_stats_wl_heur_code
  is \<open>uncurry (RETURN oo update_stats_wl_heur)\<close>
  :: \<open>k_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_stats_wl_heur_def isasat_int.case_distrib comp_def RETURN_case_isasat_int_inverse
  by sepref

sepref_def update_heur_wl_heur_code
  is \<open>uncurry (RETURN oo update_heur_wl_heur)\<close>
  :: \<open>l_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_heur_wl_heur_def isasat_int.case_distrib comp_def RETURN_case_isasat_int_inverse
  by sepref

sepref_def update_vdom_wl_heur_code
  is \<open>uncurry (RETURN oo update_vdom_wl_heur)\<close>
  :: \<open>m_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_vdom_wl_heur_def isasat_int.case_distrib comp_def RETURN_case_isasat_int_inverse
  by sepref

sepref_def update_lcount_wl_heur_code
  is \<open>uncurry (RETURN oo update_lcount_wl_heur)\<close>
  :: \<open>n_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_lcount_wl_heur_def isasat_int.case_distrib comp_def RETURN_case_isasat_int_inverse
  by sepref

sepref_def update_opts_wl_heur_code
  is \<open>uncurry (RETURN oo update_opts_wl_heur)\<close>
  :: \<open>o_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_opts_wl_heur_def isasat_int.case_distrib comp_def RETURN_case_isasat_int_inverse
  by sepref

sepref_def update_old_arena_wl_heur_code
  is \<open>uncurry (RETURN oo update_old_arena_wl_heur)\<close>
  :: \<open>p_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_old_arena_wl_heur_def isasat_int.case_distrib comp_def RETURN_case_isasat_int_inverse
  by sepref

method stuff_pre =
    sepref_to_hoare;
    case_tac x;
    vcg;
    unfold wpa_return;
    subst (asm)(2) sep_algebra_class.sep_conj_empty'[symmetric];
    rule apply_htriple_rule

method stuff_post1 =
    rule POSTCONDI;
    rule STATE_monoI

method stuff_post2 =
    unfold ex_isasat_int_iff entails_def;
    auto simp: Exists_eq_simp ex_isasat_int_iff  entails_def entails_eq_iff pure_true_conv sep_conj_left_commute;
    smt (z3) entails_def entails_eq_iff pure_true_conv sep_conj_aci(4) sep_conj_aci(5) sep_conj_left_commute

lemma RETURN_case_isasat_int_invers: \<open>(RETURN \<circ>\<circ> case_isasat_int)
   (\<lambda>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16.
  ff x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16) =
  case_isasat_int
   (\<lambda>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16.
  RETURN (ff x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16))\<close>
  by (auto intro!: ext split: isasat_int.splits)

lemmas [sepref_fr_rules] = a b c d e f g h i j k l m n  o p

sepref_definition remove_trail_wl_heur_code
  is \<open>RETURN o remove_trail_wl_heur\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a a_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_trail_wl_heur_def RETURN_case_isasat_int_invers
  by sepref

sepref_definition remove_arena_wl_heur_code
  is \<open>RETURN o remove_arena_wl_heur\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a b_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_arena_wl_heur_def RETURN_case_isasat_int_invers
  by sepref

sepref_definition remove_conflict_wl_heur_code
  is \<open>RETURN o remove_conflict_wl_heur\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a c_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_conflict_wl_heur_def RETURN_case_isasat_int_invers
  by sepref

sepref_definition remove_literals_to_update_wl_heur_code
  is \<open>RETURN o remove_literals_to_update_wl_heur\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a d_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_literals_to_update_wl_heur_def RETURN_case_isasat_int_invers
  by sepref

sepref_definition remove_watchlist_wl_heur_code
  is \<open>RETURN o remove_watchlist_wl_heur\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a e_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_watchlist_wl_heur_def RETURN_case_isasat_int_invers
  by sepref

sepref_definition remove_vmtf_wl_heur_code
  is \<open>RETURN o remove_vmtf_wl_heur\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a f_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_vmtf_wl_heur_def RETURN_case_isasat_int_invers
  by sepref

sepref_definition remove_clvls_wl_heur_code
  is \<open>RETURN o remove_clvls_wl_heur\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a g_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_clvls_wl_heur_def RETURN_case_isasat_int_invers
  by sepref

sepref_definition remove_ccach_wl_heur_code
  is \<open>RETURN o remove_ccach_wl_heur\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a h_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_ccach_wl_heur_def RETURN_case_isasat_int_invers
  by sepref

sepref_definition remove_lbd_wl_heur_code
  is \<open>RETURN o remove_lbd_wl_heur\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a i_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_lbd_wl_heur_def RETURN_case_isasat_int_invers
  by sepref

sepref_definition remove_outl_wl_heur_code
  is \<open>RETURN o remove_outl_wl_heur\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a j_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_outl_wl_heur_def RETURN_case_isasat_int_invers
  by sepref

sepref_definition remove_stats_wl_heur_code
  is \<open>RETURN o remove_stats_wl_heur\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a k_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_stats_wl_heur_def RETURN_case_isasat_int_invers
  by sepref

sepref_definition remove_heur_wl_heur_code
  is \<open>RETURN o remove_heur_wl_heur\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a l_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_heur_wl_heur_def RETURN_case_isasat_int_invers
  by sepref

sepref_definition remove_vdom_wl_heur_code
  is \<open>RETURN o remove_vdom_wl_heur\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a m_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_vdom_wl_heur_def RETURN_case_isasat_int_invers
  by sepref

sepref_definition remove_lcount_wl_heur_code
  is \<open>RETURN o remove_lcount_wl_heur\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a n_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_lcount_wl_heur_def RETURN_case_isasat_int_invers
  by sepref

sepref_definition remove_opts_wl_heur_code
  is \<open>RETURN o remove_opts_wl_heur\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a o_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_opts_wl_heur_def RETURN_case_isasat_int_invers
  by sepref

sepref_definition remove_old_arena_wl_heur_code
  is \<open>RETURN o remove_old_arena_wl_heur\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a p_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_old_arena_wl_heur_def RETURN_case_isasat_int_invers
  by sepref

end


context isasat_state
begin
lemma reconstruct_isasat[sepref_frame_match_rules]:
  \<open>hn_ctxt
     (isasat_int_assn (a_assn) (b_assn) (c_assn) (d_assn) (e_assn)
    (f_assn) (g_assn) (h_assn) (i_assn) (j_assn) (k_assn)
   (l_assn) (m_assn) (n_assn) (o_assn) (p_assn)) ax bx \<turnstile> hn_ctxt isasat_assn ax bx\<close>
    unfolding isasat_assn_def
    apply (auto split: prod.split isasat_int.splits elim: is_pureE 
      simp: sep_algebra_simps pure_part_pure_conj_eq)
      done


context
  fixes x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and
    trail_read_code :: \<open>'xa \<Rightarrow> 'q llM\<close> and
    trail_read :: \<open>'a \<Rightarrow> 'r nres\<close>
begin
definition read_trail_wl_heur_code :: \<open>_\<close> where
  \<open>read_trail_wl_heur_code xi = (case xi of
  IsaSAT_int a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 \<Rightarrow>
    trail_read_code
     a1)\<close>

definition read_trail_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _\<close> where
  \<open>read_trail_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
  trail_read x1)\<close>

context
  fixes P
  assumes trail_read[sepref_fr_rules]: \<open>(trail_read_code, trail_read) \<in> [P]\<^sub>a a_assn\<^sup>k \<rightarrow> x_assn\<close>
  notes [[sepref_register_adhoc trail_read]]
begin
sepref_definition read_trail_wl_heur_code_tmp
  is read_trail_wl_heur
  :: \<open>[P o get_trail_wl_heur]\<^sub>a isasat_assn\<^sup>k \<rightarrow> x_assn\<close>
   unfolding read_trail_wl_heur_def
   by sepref

lemmas read_trail_wl_heur_code_refine =
  read_trail_wl_heur_code_tmp.refine[unfolded read_trail_wl_heur_code_tmp_def
    read_trail_wl_heur_code_def[symmetric]]
end
end

definition read_arena_wl_heur_code where \<open>read_arena_wl_heur_code arena_read_code xi =
  (case xi of
  IsaSAT_int a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 \<Rightarrow>
  arena_read_code a2)\<close>


context
  fixes x_assn  :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and
    arena_read_code :: \<open>'xb \<Rightarrow> 'q llM\<close> and
    arena_read :: \<open>'b \<Rightarrow> 'r nres\<close> and
    P :: \<open>'b \<Rightarrow> bool\<close>
begin

definition read_arena_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _\<close> where
  \<open>read_arena_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
  arena_read x2)\<close>


context
  assumes arena_read[sepref_fr_rules]: \<open>(arena_read_code, arena_read) \<in>[P]\<^sub>a b_assn\<^sup>k \<rightarrow> x_assn\<close>
  notes [[sepref_register_adhoc arena_read]]
begin

sepref_definition read_arena_wl_heur_code_tmp
  is read_arena_wl_heur
  :: \<open>[\<lambda>S. P (get_clauses_wl_heur S)]\<^sub>a isasat_assn\<^sup>k \<rightarrow> x_assn\<close>
   unfolding read_arena_wl_heur_def
   by sepref

lemmas read_arena_wl_heur_code_refine =
  read_arena_wl_heur_code_tmp.refine[unfolded read_arena_wl_heur_code_tmp_def
    read_arena_wl_heur_code_def[symmetric]]
end
end

context
  fixes x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and
    conflict_read_code :: \<open>'xc \<Rightarrow> 'q llM\<close> and
    conflict_read :: \<open>'c \<Rightarrow> 'r nres\<close> and
    P :: \<open>'c \<Rightarrow> bool\<close>
begin

definition read_conflict_wl_heur ::\<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _\<close> where
  \<open>read_conflict_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
  conflict_read x3)\<close>

definition read_conflict_wl_heur_code :: \<open>_\<close> where
  \<open>read_conflict_wl_heur_code xi =
  (case xi of IsaSAT_int a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 \<Rightarrow>
    conflict_read_code
     a3)\<close>

context
  assumes conflict_read[sepref_fr_rules]: \<open>(conflict_read_code, conflict_read) \<in> [P]\<^sub>a c_assn\<^sup>k \<rightarrow> x_assn\<close>
  notes [[sepref_register_adhoc conflict_read]]
begin


sepref_definition read_conflict_wl_heur_code_tmp
  is read_conflict_wl_heur
  :: \<open>[\<lambda>S. P (get_conflict_wl_heur S)]\<^sub>a isasat_assn\<^sup>k \<rightarrow> x_assn\<close>
   unfolding read_conflict_wl_heur_def
   by sepref

lemmas read_conflict_wl_heur_code_refine =
  read_conflict_wl_heur_code_tmp.refine[unfolded read_conflict_wl_heur_code_tmp_def
     read_conflict_wl_heur_code_def[symmetric]]
end
end

context
  fixes x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and
    literals_to_update_read_code :: \<open>'xd \<Rightarrow> 'q llM\<close> and
    literals_to_update_read :: \<open>'d \<Rightarrow> 'r nres\<close>
begin

definition read_literals_to_update_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _\<close> where
  \<open>read_literals_to_update_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
  literals_to_update_read x4)\<close>

definition \<open>read_literals_to_update_wl_heur_code =
(\<lambda>xi. case xi of
  IsaSAT_int a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 \<Rightarrow>
    literals_to_update_read_code a4)\<close>

context
  fixes P
  assumes literals_to_update_read[sepref_fr_rules]: \<open>(literals_to_update_read_code, literals_to_update_read) \<in> [P]\<^sub>a d_assn\<^sup>k \<rightarrow> x_assn\<close>
  notes [[sepref_register_adhoc literals_to_update_read]]
begin
sepref_definition read_literals_to_update_wl_heur_code_tmp
  is read_literals_to_update_wl_heur
  :: \<open>[P o literals_to_update_wl_heur]\<^sub>a isasat_assn\<^sup>k \<rightarrow> x_assn\<close>
   unfolding read_literals_to_update_wl_heur_def
   by sepref

lemmas read_literals_to_update_wl_heur_code_refine =
  read_literals_to_update_wl_heur_code_tmp.refine[unfolded read_literals_to_update_wl_heur_code_tmp_def
     read_literals_to_update_wl_heur_code_def[symmetric]]
end

end

context
  fixes x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and
    watchlist_read_code :: \<open>'xe \<Rightarrow> 'q llM\<close> and
    watchlist_read :: \<open>'e \<Rightarrow> 'r nres\<close>
begin

definition read_watchlist_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _\<close> where
  \<open>read_watchlist_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
  watchlist_read x5)\<close>
definition \<open>read_watchlist_wl_heur_code \<equiv>
  \<lambda>xi. case xi of IsaSAT_int a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 \<Rightarrow> watchlist_read_code a5\<close>

context
  fixes P
  assumes watchlist_read[sepref_fr_rules]: \<open>(watchlist_read_code, watchlist_read) \<in> [P]\<^sub>a e_assn\<^sup>k \<rightarrow> x_assn\<close>
  notes [[sepref_register_adhoc watchlist_read]]
begin
sepref_definition read_watchlist_wl_heur_code_tmp
  is read_watchlist_wl_heur
  :: \<open>[P o get_watched_wl_heur]\<^sub>a isasat_assn\<^sup>k \<rightarrow> x_assn\<close>
   unfolding read_watchlist_wl_heur_def
   by sepref

lemmas read_watchlist_wl_heur_code_refine =
  read_watchlist_wl_heur_code_tmp.refine[unfolded read_watchlist_wl_heur_code_tmp_def
     read_watchlist_wl_heur_code_def[symmetric]]
end
end

context
  fixes x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and
    vmtf_read_code :: \<open>'xf \<Rightarrow> 'q llM\<close> and
    vmtf_read :: \<open>'f \<Rightarrow> 'r nres\<close>
begin

definition read_vmtf_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _\<close> where
  \<open>read_vmtf_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
  vmtf_read x6)\<close>

definition \<open>read_vmtf_wl_heur_code \<equiv>
\<lambda>xi. case xi of IsaSAT_int a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 \<Rightarrow> vmtf_read_code a6\<close>

context
  fixes P
  assumes vmtf_read[sepref_fr_rules]: \<open>(vmtf_read_code, vmtf_read) \<in> [P]\<^sub>a f_assn\<^sup>k \<rightarrow> x_assn\<close>
  notes [[sepref_register_adhoc vmtf_read]]
begin
sepref_definition read_vmtf_wl_heur_code_tmp
  is read_vmtf_wl_heur
  :: \<open>[P o get_vmtf_heur]\<^sub>a isasat_assn\<^sup>k \<rightarrow> x_assn\<close>
   unfolding read_vmtf_wl_heur_def
   by sepref

lemmas read_vmtf_wl_heur_code_refine =
  read_vmtf_wl_heur_code_tmp.refine[unfolded read_vmtf_wl_heur_code_tmp_def
     read_vmtf_wl_heur_code_def[symmetric]]
end
end

context
  fixes x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and
    clvls_read_code :: \<open>'xg \<Rightarrow> 'q llM\<close> and
    clvls_read :: \<open>'g \<Rightarrow> 'r nres\<close>
begin

definition read_clvls_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _\<close> where
  \<open>read_clvls_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
  clvls_read x7)\<close>

definition \<open>read_clvls_wl_heur_code \<equiv>
\<lambda>xi. case xi of IsaSAT_int a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 \<Rightarrow> clvls_read_code a7\<close>

context
  fixes P
  assumes clvls_read[sepref_fr_rules]: \<open>(clvls_read_code, clvls_read) \<in> [P]\<^sub>a g_assn\<^sup>k \<rightarrow> x_assn\<close>
  notes [[sepref_register_adhoc clvls_read]]
begin

sepref_definition read_clvls_wl_heur_code_tmp
  is read_clvls_wl_heur
  :: \<open>[P o get_count_max_lvls_heur]\<^sub>a isasat_assn\<^sup>k \<rightarrow> x_assn\<close>
   unfolding read_clvls_wl_heur_def
   by sepref

lemmas read_clvls_wl_heur_code_refine =
  read_clvls_wl_heur_code_tmp.refine[unfolded read_clvls_wl_heur_code_tmp_def
     read_clvls_wl_heur_code_def[symmetric]]
end
end

context
  fixes x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and
    ccach_read_code :: \<open>'xh \<Rightarrow> 'q llM\<close> and
    ccach_read :: \<open>'h \<Rightarrow> 'r nres\<close>
begin

definition read_ccach_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _\<close> where
  \<open>read_ccach_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
  ccach_read x8)\<close>

definition \<open>read_ccach_wl_heur_code \<equiv>
\<lambda>xi. case xi of IsaSAT_int a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 \<Rightarrow> ccach_read_code a8\<close>

context
  fixes P
  assumes ccach_read[sepref_fr_rules]: \<open>(ccach_read_code, ccach_read) \<in> [P]\<^sub>a h_assn\<^sup>k \<rightarrow> x_assn\<close>
  notes [[sepref_register_adhoc ccach_read]]
begin
sepref_definition read_ccach_wl_heur_code_tmp
  is read_ccach_wl_heur
  :: \<open>[P o get_conflict_cach]\<^sub>a isasat_assn\<^sup>k \<rightarrow> x_assn\<close>
   unfolding read_ccach_wl_heur_def
   by sepref

lemmas read_ccach_wl_heur_code_refine =
  read_ccach_wl_heur_code_tmp.refine[unfolded read_ccach_wl_heur_code_tmp_def
     read_ccach_wl_heur_code_def[symmetric]]
end
end

context
  fixes x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and
    lbd_read_code :: \<open>'xi \<Rightarrow> 'q llM\<close> and
    lbd_read :: \<open>'i \<Rightarrow> 'r nres\<close>
begin

definition read_lbd_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _\<close> where
  \<open>read_lbd_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
  lbd_read x9)\<close>
definition \<open>read_lbd_wl_heur_code \<equiv>
\<lambda>xi. case xi of IsaSAT_int a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 \<Rightarrow> lbd_read_code a9\<close>

context
  fixes P
  assumes lbd_read[sepref_fr_rules]: \<open>(lbd_read_code, lbd_read) \<in> [P]\<^sub>a i_assn\<^sup>k \<rightarrow> x_assn\<close>
  notes [[sepref_register_adhoc lbd_read]]
begin
sepref_definition read_lbd_wl_heur_code_tmp
  is read_lbd_wl_heur
  :: \<open>[P o get_lbd]\<^sub>a isasat_assn\<^sup>k \<rightarrow> x_assn\<close>
   unfolding read_lbd_wl_heur_def
   by sepref
lemmas read_lbd_wl_heur_code_refine =
  read_lbd_wl_heur_code_tmp.refine[unfolded read_lbd_wl_heur_code_tmp_def
     read_lbd_wl_heur_code_def[symmetric]]
end
end

context
  fixes x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and
    outl_read_code :: \<open>'xj \<Rightarrow> 'q llM\<close> and
    outl_read :: \<open>'j \<Rightarrow> 'r nres\<close>
begin

definition read_outl_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _\<close> where
  \<open>read_outl_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
  outl_read x10)\<close>

definition \<open>read_outl_wl_heur_code \<equiv>
\<lambda>xi. case xi of
  IsaSAT_int a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 \<Rightarrow>
    outl_read_code a10\<close>

context
  fixes P
  assumes outl_read[sepref_fr_rules]: \<open>(outl_read_code, outl_read) \<in> [P]\<^sub>a j_assn\<^sup>k \<rightarrow> x_assn\<close>
  notes [[sepref_register_adhoc outl_read]]
begin
sepref_definition read_outl_wl_heur_code_tmp
  is read_outl_wl_heur
  :: \<open>[P o get_outlearned_heur]\<^sub>a isasat_assn\<^sup>k \<rightarrow> x_assn\<close>
   unfolding read_outl_wl_heur_def
   by sepref

lemmas read_outl_wl_heur_code_refine =
  read_outl_wl_heur_code_tmp.refine[unfolded read_outl_wl_heur_code_tmp_def
     read_outl_wl_heur_code_def[symmetric]]
end
end

context
  fixes x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and
    stats_read_code :: \<open>'xk \<Rightarrow> 'q llM\<close> and
    stats_read :: \<open>'k \<Rightarrow> 'r nres\<close>
begin

definition read_stats_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _\<close> where
  \<open>read_stats_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
  stats_read x11)\<close>
definition \<open>read_stats_wl_heur_code \<equiv>
\<lambda>xi. case xi of IsaSAT_int a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 \<Rightarrow> stats_read_code a11\<close>

context
  fixes P
  assumes stats_read[sepref_fr_rules]: \<open>(stats_read_code, stats_read) \<in>[P]\<^sub>a  k_assn\<^sup>k \<rightarrow> x_assn\<close>
  notes [[sepref_register_adhoc stats_read]]
begin
sepref_definition read_stats_wl_heur_code_tmp
  is read_stats_wl_heur
  :: \<open>[P o get_stats_heur]\<^sub>a isasat_assn\<^sup>k \<rightarrow> x_assn\<close>
   unfolding read_stats_wl_heur_def
   by sepref

lemmas read_stats_wl_heur_code_refine =
  read_stats_wl_heur_code_tmp.refine[unfolded read_stats_wl_heur_code_tmp_def
     read_stats_wl_heur_code_def[symmetric]]
end
end

context
  fixes x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and
    heur_read_code :: \<open>'xl \<Rightarrow> 'q llM\<close> and
    heur_read :: \<open>'l \<Rightarrow> 'r nres\<close>
begin

definition read_heur_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _\<close> where
  \<open>read_heur_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
  heur_read x12)\<close>

definition \<open>read_heur_wl_heur_code \<equiv>
\<lambda>xi. case xi of
  IsaSAT_int a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 \<Rightarrow>
    heur_read_code a12\<close>
context
  fixes P
  assumes heur_read[sepref_fr_rules]: \<open>(heur_read_code, heur_read) \<in> [P]\<^sub>a  l_assn\<^sup>k \<rightarrow> x_assn\<close>
  notes [[sepref_register_adhoc heur_read]]
begin
sepref_definition read_heur_wl_heur_code_tmp
  is read_heur_wl_heur
  :: \<open>[P o get_heur]\<^sub>a isasat_assn\<^sup>k \<rightarrow> x_assn\<close>
   unfolding read_heur_wl_heur_def
   by sepref
lemmas read_heur_wl_heur_code_refine =
  read_heur_wl_heur_code_tmp.refine[unfolded read_heur_wl_heur_code_tmp_def
     read_heur_wl_heur_code_def[symmetric]]
end
end

context
  fixes x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and
    vdom_read_code :: \<open>'xm \<Rightarrow> 'q llM\<close> and
    vdom_read :: \<open>'m \<Rightarrow> 'r nres\<close>
begin

definition read_vdom_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _\<close> where
  \<open>read_vdom_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
  vdom_read x13)\<close>
definition \<open>read_vdom_wl_heur_code \<equiv>
\<lambda>xi. case xi of
  IsaSAT_int a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 \<Rightarrow>
    vdom_read_code a13\<close>

context
  fixes P
  assumes vdom_read[sepref_fr_rules]: \<open>(vdom_read_code, vdom_read) \<in> [P]\<^sub>a m_assn\<^sup>k \<rightarrow> x_assn\<close>
  notes [[sepref_register_adhoc vdom_read]]
begin
sepref_definition read_vdom_wl_heur_code_tmp
  is read_vdom_wl_heur
  :: \<open>[P o get_aivdom]\<^sub>a isasat_assn\<^sup>k \<rightarrow> x_assn\<close>
   unfolding read_vdom_wl_heur_def
   by sepref

lemmas read_vdom_wl_heur_code_refine =
  read_vdom_wl_heur_code_tmp.refine[unfolded read_vdom_wl_heur_code_tmp_def
     read_vdom_wl_heur_code_def[symmetric]]
end
end

context
  fixes x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and
    lcount_read_code :: \<open>'xn \<Rightarrow> 'q llM\<close> and
    lcount_read :: \<open>'n \<Rightarrow> 'r nres\<close>
begin

definition read_lcount_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _\<close> where
  \<open>read_lcount_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
  lcount_read x14)\<close>
definition \<open>read_lcount_wl_heur_code \<equiv>
\<lambda>xi. case xi of
  IsaSAT_int a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 \<Rightarrow>
    lcount_read_code a14\<close>

context
  fixes P
  assumes lcount_read[sepref_fr_rules]: \<open>(lcount_read_code, lcount_read) \<in> [P]\<^sub>a n_assn\<^sup>k \<rightarrow> x_assn\<close>
  notes [[sepref_register_adhoc lcount_read]]
begin
sepref_definition read_lcount_wl_heur_code_tmp
  is read_lcount_wl_heur
  :: \<open>[P o get_learned_count]\<^sub>a isasat_assn\<^sup>k \<rightarrow> x_assn\<close>
   unfolding read_lcount_wl_heur_def
   by sepref

lemmas read_lcount_wl_heur_code_refine =
  read_lcount_wl_heur_code_tmp.refine[unfolded read_lcount_wl_heur_code_tmp_def
     read_lcount_wl_heur_code_def[symmetric]]
end
end

context
  fixes x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and
    opts_read_code :: \<open>'xo \<Rightarrow> 'q llM\<close> and
    opts_read :: \<open>'o \<Rightarrow> 'r nres\<close>
begin

definition read_opts_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _\<close> where
  \<open>read_opts_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
  opts_read x15)\<close>
definition \<open>read_opts_wl_heur_code \<equiv>
\<lambda>xi. case xi of
  IsaSAT_int a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 \<Rightarrow>
    opts_read_code a15\<close>
context
  fixes P
  assumes opts_read[sepref_fr_rules]: \<open>(opts_read_code, opts_read) \<in> [P]\<^sub>a o_assn\<^sup>k \<rightarrow> x_assn\<close>
  notes [[sepref_register_adhoc opts_read]]
begin
sepref_definition read_opts_wl_heur_code_tmp
  is read_opts_wl_heur
  :: \<open>[P o get_opts]\<^sub>a isasat_assn\<^sup>k \<rightarrow> x_assn\<close>
   unfolding read_opts_wl_heur_def
   by sepref
lemmas read_opts_wl_heur_code_refine =
  read_opts_wl_heur_code_tmp.refine[unfolded read_opts_wl_heur_code_tmp_def
     read_opts_wl_heur_code_def[symmetric]]
end
end

context
  fixes x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and
    old_arena_read_code :: \<open>'xp \<Rightarrow> 'q llM\<close> and
    old_arena_read :: \<open>'p \<Rightarrow> 'r nres\<close>
begin

definition read_old_arena_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _\<close> where
  \<open>read_old_arena_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
  old_arena_read x16)\<close>

definition \<open>read_old_arena_wl_heur_code \<equiv>
\<lambda>xi. case xi of
  IsaSAT_int a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 x \<Rightarrow>
    old_arena_read_code x\<close>

context
  fixes P
  assumes old_arena_read[sepref_fr_rules]: \<open>(old_arena_read_code, old_arena_read) \<in> [P]\<^sub>a p_assn\<^sup>k \<rightarrow> x_assn\<close>
  notes [[sepref_register_adhoc old_arena_read]]
begin
sepref_definition read_old_arena_wl_heur_code_tmp
  is read_old_arena_wl_heur
  :: \<open>[P o get_old_arena]\<^sub>a isasat_assn\<^sup>k \<rightarrow> x_assn\<close>
   unfolding read_old_arena_wl_heur_def
   by sepref

lemmas read_old_arena_wl_heur_code_refine =
  read_old_arena_wl_heur_code_tmp.refine[unfolded read_old_arena_wl_heur_code_tmp_def
     read_old_arena_wl_heur_code_def[symmetric]]
end
end

end


text \<open>The following constants are not useful for the initialisation for the solver, but only as temporary replacement
  for values in state.\<close>
definition bottom_trail :: trail_pol where
  \<open>bottom_trail = do {
     let M0 = [] in
     let cs = [] in
     let M = replicate 0 UNSET in
     let M' = replicate 0 0 in
     let M'' = replicate 0 1 in
    ((M0, M, M', M'', 0, cs))
}\<close>

definition extract_trail_wl_heur where
  \<open>extract_trail_wl_heur = isasat_state_ops.remove_trail_wl_heur bottom_trail\<close>

sepref_def bottom_trail_code
  is \<open>uncurry0 (RETURN bottom_trail)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a trail_pol_fast_assn\<close>
  unfolding bottom_trail_def trail_pol_fast_assn_def
  apply (rewrite in \<open>let _ = \<hole> in _\<close> annotate_assn[where A=\<open>arl64_assn unat_lit_assn\<close>])
  apply (rewrite in \<open>let _ = \<hole> in _\<close> al_fold_custom_empty[where 'l=64])
  apply (rewrite in \<open>let _ = _; _ = \<hole> in _\<close> al_fold_custom_empty[where 'l=64])
  apply (rewrite in \<open>let _ = _; _ = \<hole> in _\<close> annotate_assn[where A=\<open>arl64_assn uint32_nat_assn\<close>])

  apply (rewrite in \<open>let _ = _;_ = \<hole> in _\<close> annotate_assn[where A=\<open>larray64_assn (tri_bool_assn)\<close>])
  apply (rewrite in \<open>let _ = _;_ = _;_ = \<hole> in _\<close> annotate_assn[where A=\<open>larray64_assn uint32_nat_assn\<close>])
  apply (rewrite in \<open>let _ = _ in _\<close> larray_fold_custom_replicate)
  apply (rewrite in \<open>let _ = _ in _\<close> larray_fold_custom_replicate)
  apply (rewrite in \<open>let _ = _ in _\<close> larray_fold_custom_replicate)
  apply (rewrite at \<open>(_, \<hole>, _)\<close> unat_const_fold[where 'a=32])
  apply (rewrite at \<open>(op_larray_custom_replicate _ \<hole>)\<close> unat_const_fold[where 'a=32])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  supply [[goals_limit = 1]]
  by sepref

definition bottom_arena :: \<open>arena\<close> where
  \<open>bottom_arena = []\<close>

definition extract_arena_wl_heur where
  \<open>extract_arena_wl_heur = isasat_state_ops.remove_arena_wl_heur bottom_arena\<close>

sepref_def bottom_arena_code
  is \<open>uncurry0 (RETURN bottom_arena)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a arena_fast_assn\<close>
  unfolding bottom_arena_def al_fold_custom_empty[where 'l=64]
  by sepref

definition bottom_conflict :: \<open>conflict_option_rel\<close> where
  \<open>bottom_conflict = (True, 0, replicate 0 NOTIN)\<close>

definition extract_conflict_wl_heur where
  \<open>extract_conflict_wl_heur = isasat_state_ops.remove_conflict_wl_heur bottom_conflict\<close>

sepref_def bottom_conflict_code
  is \<open>uncurry0 (RETURN bottom_conflict)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a conflict_option_rel_assn\<close>
  unfolding bottom_conflict_def
    conflict_option_rel_assn_def lookup_clause_rel_assn_def array_fold_custom_replicate
  apply (rewrite at \<open>(_, \<hole>, _)\<close> unat_const_fold[where 'a=32])
  apply (annot_snat_const \<open>TYPE(32)\<close>)
  by sepref

definition bottom_decision_level :: nat where
  \<open>bottom_decision_level = 0\<close>

definition extract_literals_to_update_wl_heur :: \<open>_ \<Rightarrow> _\<close> where
  \<open>extract_literals_to_update_wl_heur = isasat_state_ops.remove_literals_to_update_wl_heur bottom_decision_level\<close>

sepref_def bottom_decision_level_code
  is \<open>uncurry0 (RETURN bottom_decision_level)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding bottom_decision_level_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

definition bottom_watchlist :: \<open>(nat) watcher list list\<close> where
  \<open>bottom_watchlist = replicate 0 []\<close>

definition extract_watchlist_wl_heur where
  \<open>extract_watchlist_wl_heur = isasat_state_ops.remove_watchlist_wl_heur bottom_watchlist\<close>

sepref_def bottom_watchlist_code
  is \<open>uncurry0 (RETURN bottom_watchlist)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a watchlist_fast_assn\<close>
  unfolding bottom_watchlist_def aal_fold_custom_empty[where 'l=64 and 'll=64]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

definition bottom_atom where
  \<open>bottom_atom = 0\<close>
lemma [sepref_fr_rules]: \<open>(uncurry0 (Mreturn 0), uncurry0 (RETURN bottom_atom)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a atom_assn\<close>
  unfolding bottom_atom_def
  apply sepref_to_hoare
  apply vcg
  apply (auto simp: atom_rel_def unat_rel_def unat.rel_def br_def entails_def ENTAILS_def)
  by (smt (verit, best) pure_true_conv rel_simps(51) sep.add_0)

definition bottom_vmtf :: \<open>isa_vmtf_remove_int\<close> where
  \<open>bottom_vmtf = ((replicate 0 (VMTF_Node 0 None None), 0, bottom_atom, bottom_atom, None), [], replicate 0 False)\<close>

definition extract_vmtf_wl_heur where
  \<open>extract_vmtf_wl_heur = isasat_state_ops.remove_vmtf_wl_heur bottom_vmtf\<close>

sepref_def bottom_vmtf_code
  is \<open>uncurry0 (RETURN bottom_vmtf)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a vmtf_remove_assn\<close>
  unfolding bottom_vmtf_def
  apply (rewrite in \<open>((\<hole>, _, _, _, _), _, _)\<close> array_fold_custom_replicate)
  unfolding
   atom.fold_option array_fold_custom_replicate vmtf_remove_assn_def
    al_fold_custom_empty[where 'l=64]
  apply (rewrite at 0 in \<open>VMTF_Node \<hole>\<close> unat_const_fold[where 'a=64])
  apply (rewrite at \<open>(_, \<hole>, _, _)\<close> unat_const_fold[where 'a=64])
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  apply (rewrite at \<open>(\<hole>, _, _)\<close> annotate_assn[where A = vmtf_assn])
  apply (rewrite at \<open>(_, \<hole>, _)\<close> annotate_assn[where A =\<open>al_assn atom_assn\<close>])
  apply (rewrite at \<open>(_, _, \<hole>)\<close> annotate_assn[where A =\<open>phase_saver'_assn\<close>])
  by sepref

definition bottom_clvls :: \<open>nat\<close> where
  \<open>bottom_clvls = 0\<close>

definition extract_clvls_wl_heur where
  \<open>extract_clvls_wl_heur = isasat_state_ops.remove_clvls_wl_heur bottom_clvls\<close>

sepref_def bottom_clvls_code
  is \<open>uncurry0 (RETURN bottom_clvls)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a uint32_nat_assn\<close>
  unfolding bottom_clvls_def
  apply (annot_unat_const \<open>TYPE(32)\<close>)
  by sepref

definition bottom_ccach :: \<open>minimize_status list \<times> nat list\<close> where
  \<open>bottom_ccach = (replicate 0 SEEN_UNKNOWN, [])\<close>

definition extract_ccach_wl_heur where
  \<open>extract_ccach_wl_heur = isasat_state_ops.remove_ccach_wl_heur bottom_ccach\<close>

sepref_def bottom_ccach_code
  is \<open>uncurry0 (RETURN bottom_ccach)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a cach_refinement_l_assn\<close>
  unfolding bottom_ccach_def cach_refinement_l_assn_def array_fold_custom_replicate
  apply (rewrite at \<open>(_, \<hole>)\<close> al_fold_custom_empty[where 'l=64])
  apply (rewrite at \<open>(\<hole>, _)\<close> annotate_assn[where A = \<open>IICF_Array.array_assn minimize_status_assn\<close>])
  apply (annot_snat_const \<open>TYPE(32)\<close>)
  by sepref

definition extract_lbd_wl_heur where
  \<open>extract_lbd_wl_heur = isasat_state_ops.remove_lbd_wl_heur empty_lbd\<close>

definition bottom_outl :: \<open>out_learned\<close> where
  \<open>bottom_outl = []\<close>

definition extract_outl_wl_heur where
  \<open>extract_outl_wl_heur = isasat_state_ops.remove_outl_wl_heur bottom_outl\<close>

sepref_def bottom_outl_code
  is \<open>uncurry0 (RETURN bottom_outl)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a out_learned_assn\<close>
  unfolding bottom_outl_def cach_refinement_l_assn_def array_fold_custom_replicate
  apply (rewrite at \<open>(\<hole>)\<close> al_fold_custom_empty[where 'l=64])
  by sepref

definition bottom_stats :: \<open>isasat_stats\<close> where
  \<open>bottom_stats = Stats (0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0)\<close>

definition extract_stats_wl_heur where
  \<open>extract_stats_wl_heur = isasat_state_ops.remove_stats_wl_heur bottom_stats\<close>

sepref_def bottom_stats_code
  is \<open>uncurry0 (RETURN bottom_stats)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a stats_assn\<close>
  unfolding bottom_stats_def
  by sepref

find_theorems Restart_Heuristics RETURN

definition bottom_heur_int :: \<open> restart_heuristics\<close> where
  \<open>bottom_heur_int = (
  let \<phi> = replicate 0 False in
  let fema = ema_init (0) in
  let sema = ema_init (0) in let ccount = restart_info_init in
  let n = 0  in
  (fema, sema, ccount, 0, (\<phi>, 0, replicate n False, 0, replicate n False, 10000, 1000, 1), reluctant_init, False))
\<close>
sepref_def bottom_heur_int_code
  is \<open>uncurry0 (RETURN bottom_heur_int)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a heuristic_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding bottom_heur_int_def heuristic_int_assn_def phase_heur_assn_def
  apply (rewrite in \<open>(replicate _ False, _)\<close> annotate_assn[where A=phase_saver'_assn])
  apply (rewrite in \<open>(replicate _ False, _)\<close> array_fold_custom_replicate)
  apply (rewrite at \<open>(_, _, _, \<hole>, _)\<close> annotate_assn[where A=phase_saver'_assn])
  apply (rewrite in \<open>(_, _, \<hole>, _)\<close> array_fold_custom_replicate)
  apply (rewrite at \<open>(_, \<hole>, _,_,_,_)\<close> snat_const_fold[where 'a=64])
  apply (rewrite at \<open>(_, _,_,\<hole>, _,_,_)\<close> snat_const_fold[where 'a=64])
  apply (rewrite in \<open>let _ =\<hole> in _\<close> annotate_assn[where A=phase_saver_assn])
  unfolding larray_fold_custom_replicate
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

definition bottom_heur :: \<open>_\<close> where
  \<open>bottom_heur = Restart_Heuristics (bottom_heur_int)\<close>

definition extract_heur_wl_heur where
  \<open>extract_heur_wl_heur = isasat_state_ops.remove_heur_wl_heur bottom_heur\<close>

sepref_def bottom_heur_code
  is \<open>uncurry0 (RETURN bottom_heur)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a heuristic_assn\<close>
  supply [[goals_limit=1]]
  unfolding bottom_heur_def
  by sepref

definition bottom_vdom :: \<open>_\<close> where
  \<open>bottom_vdom = AIvdom_init [] [] []\<close>

definition extract_vdom_wl_heur where
  \<open>extract_vdom_wl_heur = isasat_state_ops.remove_vdom_wl_heur bottom_vdom\<close>

sepref_def bottom_vdom_code
  is \<open>uncurry0 (RETURN bottom_vdom)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a aivdom_assn\<close>
  supply [[goals_limit=1]]
  unfolding bottom_vdom_def
  unfolding al_fold_custom_empty[where 'l=64]
  by sepref

definition bottom_lcount :: \<open>clss_size\<close> where
  \<open>bottom_lcount = (0, 0, 0, 0, 0)\<close>

definition extract_lcount_wl_heur where
  \<open>extract_lcount_wl_heur = isasat_state_ops.remove_lcount_wl_heur bottom_lcount\<close>

sepref_def bottom_lcount_code
  is \<open>uncurry0 (RETURN bottom_lcount)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a lcount_assn\<close>
  supply [[goals_limit=1]]
  unfolding bottom_lcount_def lcount_assn_def
  unfolding al_fold_custom_empty[where 'l=64]
  apply (annot_unat_const \<open>TYPE(64)\<close>)
  by sepref

definition bottom_opts :: \<open>opts\<close> where
  \<open>bottom_opts = IsaOptions False False False 0 0 0 0 0 0 0\<close>

definition extract_opts_wl_heur where
  \<open>extract_opts_wl_heur = isasat_state_ops.remove_opts_wl_heur bottom_opts\<close>

sepref_def bottom_opts_code
  is \<open>uncurry0 (RETURN bottom_opts)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a opts_assn\<close>
  supply [[goals_limit=1]]
  unfolding bottom_opts_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

definition bottom_old_arena :: \<open>arena\<close> where
  \<open>bottom_old_arena = []\<close>

definition extract_old_arena_wl_heur where
  \<open>extract_old_arena_wl_heur = isasat_state_ops.remove_old_arena_wl_heur bottom_old_arena\<close>

sepref_def bottom_old_arena_code
  is \<open>uncurry0 (RETURN bottom_old_arena)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a arena_fast_assn\<close>
  supply [[goals_limit=1]]
  unfolding bottom_old_arena_def  al_fold_custom_empty[where 'l=64]
  by sepref

schematic_goal free_trail_pol_fast_assn[sepref_frame_free_rules]: \<open>MK_FREE trail_pol_fast_assn ?a\<close>
    unfolding trail_pol_fast_assn_def
    by synthesize_free

sepref_def free_trail_pol_fast
  is \<open>mop_free\<close>
  :: \<open>trail_pol_fast_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_trail_pol_fast_assn2: \<open>MK_FREE trail_pol_fast_assn free_trail_pol_fast\<close>
  unfolding free_trail_pol_fast_def
  by (rule back_subst[of \<open>MK_FREE trail_pol_fast_assn\<close>, OF free_trail_pol_fast_assn])
    (auto intro!: ext)
 
schematic_goal free_arena_fast_assn[sepref_frame_free_rules]: \<open>MK_FREE arena_fast_assn ?a\<close>
    by synthesize_free

sepref_def free_arena_fast
  is \<open>mop_free\<close>
  :: \<open>arena_fast_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_arena_fast_assn2: \<open>MK_FREE arena_fast_assn free_arena_fast\<close>
  unfolding free_arena_fast_def
  by (rule back_subst[of \<open>MK_FREE arena_fast_assn\<close>, OF free_arena_fast_assn])
    (auto intro!: ext)

schematic_goal free_conflict_option_rel_assn[sepref_frame_free_rules]: \<open>MK_FREE conflict_option_rel_assn ?a\<close>
    by synthesize_free

sepref_def free_conflict_option_rel
  is \<open>mop_free\<close>
  :: \<open>conflict_option_rel_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_conflict_option_rel_assn2: \<open>MK_FREE conflict_option_rel_assn free_conflict_option_rel\<close>
  unfolding free_conflict_option_rel_def
  by (rule back_subst[of \<open>MK_FREE conflict_option_rel_assn\<close>, OF free_conflict_option_rel_assn])
    (auto intro!: ext)

schematic_goal free_sint64_nat_assn[sepref_frame_free_rules]: \<open>MK_FREE sint64_nat_assn ?a\<close>
    by synthesize_free

sepref_def free_sint64_nat
  is \<open>mop_free\<close>
  :: \<open>sint64_nat_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_sint64_nat_assn_assn2: \<open>MK_FREE sint64_nat_assn free_sint64_nat\<close>
  unfolding free_sint64_nat_def
  by (rule back_subst[of \<open>MK_FREE sint64_nat_assn\<close>, OF free_sint64_nat_assn])
    (auto intro!: ext)

schematic_goal free_watchlist_fast_assn[sepref_frame_free_rules]: \<open>MK_FREE watchlist_fast_assn ?a\<close>
    by synthesize_free

sepref_def free_watchlist_fast
  is \<open>mop_free\<close>
  :: \<open>watchlist_fast_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_watchlist_fast_assn2: \<open>MK_FREE watchlist_fast_assn free_watchlist_fast\<close>
  unfolding free_watchlist_fast_def
  by (rule back_subst[of \<open>MK_FREE watchlist_fast_assn\<close>, OF free_watchlist_fast_assn])
    (auto intro!: ext)

schematic_goal free_vmtf_remove_assn[sepref_frame_free_rules]: \<open>MK_FREE vmtf_remove_assn ?a\<close>
    unfolding vmtf_remove_assn_def
    by synthesize_free

sepref_def free_vmtf_remove
  is \<open>mop_free\<close>
  :: \<open>vmtf_remove_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_vmtf_remove_assn2: \<open>MK_FREE vmtf_remove_assn free_vmtf_remove\<close>
  unfolding free_vmtf_remove_def
  by (rule back_subst[of \<open>MK_FREE vmtf_remove_assn\<close>, OF free_vmtf_remove_assn])
    (auto intro!: ext)

schematic_goal free_uint32_nat_assn[sepref_frame_free_rules]: \<open>MK_FREE uint32_nat_assn ?a\<close>
    by synthesize_free

sepref_def free_uint32_nat
  is \<open>mop_free\<close>
  :: \<open>uint32_nat_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_uint32_nat_assn2: \<open>MK_FREE uint32_nat_assn free_uint32_nat\<close>
  unfolding free_uint32_nat_def
  by (rule back_subst[of \<open>MK_FREE uint32_nat_assn\<close>, OF free_uint32_nat_assn])
    (auto intro!: ext)
 
schematic_goal free_cach_refinement_l_assn[sepref_frame_free_rules]: \<open>MK_FREE cach_refinement_l_assn ?a\<close>
    by synthesize_free

sepref_def free_cach_refinement_l
  is \<open>mop_free\<close>
  :: \<open>cach_refinement_l_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_cach_refinement_l_assn2: \<open>MK_FREE cach_refinement_l_assn free_cach_refinement_l\<close>
  unfolding free_cach_refinement_l_def
  by (rule back_subst[of \<open>MK_FREE cach_refinement_l_assn\<close>, OF free_cach_refinement_l_assn])
    (auto intro!: ext)
 
schematic_goal free_lbd_assn[sepref_frame_free_rules]: \<open>MK_FREE lbd_assn ?a\<close>
    by synthesize_free

sepref_def free_lbd
  is \<open>mop_free\<close>
  :: \<open>lbd_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_lbd_assn2: \<open>MK_FREE lbd_assn free_lbd\<close>
  unfolding free_lbd_def
  by (rule back_subst[of \<open>MK_FREE lbd_assn\<close>, OF free_lbd_assn])
    (auto intro!: ext)
 
schematic_goal free_outl_assn[sepref_frame_free_rules]: \<open>MK_FREE out_learned_assn ?a\<close>
    by synthesize_free

sepref_def free_outl
  is \<open>mop_free\<close>
  :: \<open>out_learned_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_outl_assn2: \<open>MK_FREE out_learned_assn free_outl\<close>
  unfolding free_outl_def
  by (rule back_subst[of \<open>MK_FREE out_learned_assn\<close>, OF free_outl_assn])
    (auto intro!: ext)

schematic_goal free_heur_assn[sepref_frame_free_rules]: \<open>MK_FREE heuristic_assn ?a\<close>
    unfolding heuristic_assn_def code_hider_assn_def
    by synthesize_free

sepref_def free_heur
  is \<open>mop_free\<close>
  :: \<open>heuristic_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_heur_assn2: \<open>MK_FREE heuristic_assn free_heur\<close>
  unfolding free_heur_def
  by (rule back_subst[of \<open>MK_FREE heuristic_assn\<close>, OF free_heur_assn])
    (auto intro!: ext)

schematic_goal free_stats_assn[sepref_frame_free_rules]: \<open>MK_FREE stats_assn ?a\<close>
    unfolding stats_assn_def code_hider_assn_def
    by synthesize_free

sepref_def free_stats
  is \<open>mop_free\<close>
  :: \<open>stats_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_stats_assn2: \<open>MK_FREE stats_assn free_stats\<close>
  unfolding free_stats_def
  by (rule back_subst[of \<open>MK_FREE stats_assn\<close>, OF free_stats_assn])
    (auto intro!: ext)

schematic_goal free_vdom_assn[sepref_frame_free_rules]: \<open>MK_FREE aivdom_assn ?a\<close>
    unfolding aivdom_assn_def code_hider_assn_def
    by synthesize_free

sepref_def free_vdom
  is \<open>mop_free\<close>
  :: \<open>aivdom_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_vdom_assn2: \<open>MK_FREE aivdom_assn free_vdom\<close>
  unfolding free_vdom_def
  by (rule back_subst[of \<open>MK_FREE aivdom_assn\<close>, OF free_vdom_assn])
    (auto intro!: ext)

schematic_goal free_lcount_assn[sepref_frame_free_rules]: \<open>MK_FREE lcount_assn ?a\<close>
    unfolding lcount_assn_def code_hider_assn_def
    by synthesize_free

sepref_def free_lcount
  is \<open>mop_free\<close>
  :: \<open>lcount_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_lcount_assn2: \<open>MK_FREE lcount_assn free_lcount\<close>
  unfolding free_lcount_def
  by (rule back_subst[of \<open>MK_FREE lcount_assn\<close>, OF free_lcount_assn])
    (auto intro!: ext)

schematic_goal free_opts_assn[sepref_frame_free_rules]: \<open>MK_FREE opts_assn ?a\<close>
    unfolding opts_assn_def code_hider_assn_def opts_rel_assn_def
    by synthesize_free

sepref_def free_opts
  is \<open>mop_free\<close>
  :: \<open>opts_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_opts_assn2: \<open>MK_FREE opts_assn free_opts\<close>
  unfolding free_opts_def
  by (rule back_subst[of \<open>MK_FREE opts_assn\<close>, OF free_opts_assn])
    (auto intro!: ext)

schematic_goal free_old_arena_fast_assn[sepref_frame_free_rules]: \<open>MK_FREE arena_fast_assn ?a\<close>
    by synthesize_free

sepref_def free_old_arena_fast
  is \<open>mop_free\<close>
  :: \<open>arena_fast_assn\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_old_arena_fast_assn2: \<open>MK_FREE arena_fast_assn free_old_arena_fast\<close>
  unfolding free_old_arena_fast_def free_arena_fast_def
  by (rule back_subst[of \<open>MK_FREE arena_fast_assn\<close>, OF free_old_arena_fast_assn])
    (auto intro!: ext)

global_interpretation isasat_state where
  a_assn = trail_pol_fast_assn and
  b_assn = arena_fast_assn and
  c_assn = conflict_option_rel_assn and
  d_assn = sint64_nat_assn and
  e_assn = watchlist_fast_assn and
  f_assn = vmtf_remove_assn and
  g_assn = uint32_nat_assn and
  h_assn = cach_refinement_l_assn and
  i_assn = lbd_assn and
  j_assn = out_learned_assn and
  k_assn = stats_assn and
  l_assn = heuristic_assn and
  m_assn = aivdom_assn and
  n_assn = lcount_assn and
  o_assn = opts_assn and
  p_assn = arena_fast_assn and
  a_default = bottom_trail and
  a = \<open>bottom_trail_code\<close> and
  a_free = free_trail_pol_fast and
  b_default = bottom_arena and
  b = \<open>bottom_arena_code\<close> and
  b_free = free_arena_fast and
  c_default = bottom_conflict and
  c = \<open>bottom_conflict_code\<close> and
  c_free = free_conflict_option_rel and
  d_default = \<open>bottom_decision_level\<close> and
  d = \<open>(bottom_decision_level_code)\<close> and
  d_free = \<open>free_sint64_nat\<close> and
  e_default = bottom_watchlist and
  e = \<open>bottom_watchlist_code\<close> and
  e_free = free_watchlist_fast and
  f_default = bottom_vmtf and
  f = \<open>bottom_vmtf_code\<close> and
  f_free = free_vmtf_remove and
  g_default = bottom_clvls and
  g = \<open>bottom_clvls_code\<close>and
  g_free = free_uint32_nat and
  h_default = bottom_ccach and
  h = \<open>bottom_ccach_code\<close> and
  h_free = free_cach_refinement_l and
  i_default = empty_lbd and
  i = \<open>empty_lbd_code\<close> and
  i_free = free_lbd and
  j_default = bottom_outl and
  j = \<open>bottom_outl_code\<close> and
  j_free = free_outl and
  k_default = bottom_stats and
  k = \<open>bottom_stats_code\<close> and
  k_free = free_stats and
  l_default = bottom_heur and
  l = \<open>bottom_heur_code\<close> and
  l_free = free_heur and
  m_default = bottom_vdom and
  m = \<open>bottom_vdom_code\<close> and
  m_free = free_vdom and
  n_default = bottom_lcount and
  n = \<open>bottom_lcount_code\<close> and
  n_free = free_lcount and
  ko_default = bottom_opts and
  ko = \<open>bottom_opts_code\<close> and
  o_free = free_opts and
  p_default = bottom_old_arena and
  p = \<open>bottom_old_arena_code\<close> and
  p_free = free_old_arena_fast
  rewrites
    \<open>isasat_assn \<equiv> isasat_bounded_assn\<close> and
    \<open>remove_trail_wl_heur \<equiv> extract_trail_wl_heur\<close> and
    \<open>remove_arena_wl_heur \<equiv> extract_arena_wl_heur\<close> and
    \<open>remove_conflict_wl_heur \<equiv> extract_conflict_wl_heur\<close> and
    \<open>remove_literals_to_update_wl_heur \<equiv> extract_literals_to_update_wl_heur\<close> and
    \<open>remove_watchlist_wl_heur \<equiv> extract_watchlist_wl_heur\<close> and
    \<open>remove_vmtf_wl_heur \<equiv> extract_vmtf_wl_heur\<close> and
    \<open>remove_clvls_wl_heur \<equiv> extract_clvls_wl_heur\<close> and
    \<open>remove_ccach_wl_heur \<equiv> extract_ccach_wl_heur\<close> and
    \<open>remove_lbd_wl_heur \<equiv> extract_lbd_wl_heur\<close> and
    \<open>remove_outl_wl_heur \<equiv> extract_outl_wl_heur\<close> and
    \<open>remove_stats_wl_heur \<equiv> extract_stats_wl_heur\<close> and
    \<open>remove_heur_wl_heur \<equiv> extract_heur_wl_heur\<close> and
    \<open>remove_vdom_wl_heur \<equiv> extract_vdom_wl_heur\<close> and
    \<open>remove_lcount_wl_heur \<equiv> extract_lcount_wl_heur\<close> and
    \<open>remove_opts_wl_heur \<equiv> extract_opts_wl_heur\<close> and
    \<open>remove_old_arena_wl_heur \<equiv> extract_old_arena_wl_heur\<close>
  apply unfold_locales
  subgoal by (rule bottom_trail_code.refine)
  subgoal by (rule bottom_arena_code.refine)
  subgoal by (rule bottom_conflict_code.refine)
  subgoal by (rule bottom_decision_level_code.refine)
  subgoal by (rule bottom_watchlist_code.refine)
  subgoal by (rule bottom_vmtf_code.refine)
  subgoal by (rule bottom_clvls_code.refine)
  subgoal by (rule bottom_ccach_code.refine)
  subgoal by (rule empty_lbd_hnr)
  subgoal by (rule bottom_outl_code.refine)
  subgoal by (rule bottom_stats_code.refine)
  subgoal by (rule bottom_heur_code.refine)
  subgoal by (rule bottom_vdom_code.refine)
  subgoal by (rule bottom_lcount_code.refine)
  subgoal by (rule bottom_opts_code.refine)
  subgoal by (rule bottom_old_arena_code.refine)
  subgoal by (rule free_trail_pol_fast_assn2)
  subgoal by (rule free_arena_fast_assn2)
  subgoal by (rule free_conflict_option_rel_assn2)
  subgoal by (rule free_sint64_nat_assn_assn2)
  subgoal by (rule free_watchlist_fast_assn2)
  subgoal by (rule free_vmtf_remove_assn2)
  subgoal by (rule free_uint32_nat_assn2)
  subgoal by (rule free_cach_refinement_l_assn2)
  subgoal by (rule free_lbd_assn2)
  subgoal by (rule free_outl_assn2)
  subgoal by (rule free_stats_assn2)
  subgoal by (rule free_heur_assn2)
  subgoal by (rule free_vdom_assn2)
  subgoal by (rule free_lcount_assn2)
  subgoal by (rule free_opts_assn2)
  subgoal by (rule free_old_arena_fast_assn2)
  subgoal unfolding isasat_bounded_assn_def isasat_state_ops.isasat_assn_def .
  subgoal unfolding extract_trail_wl_heur_def .
  subgoal unfolding extract_arena_wl_heur_def .
  subgoal unfolding extract_conflict_wl_heur_def .
  subgoal unfolding extract_literals_to_update_wl_heur_def .
  subgoal unfolding extract_watchlist_wl_heur_def .
  subgoal unfolding extract_vmtf_wl_heur_def .
  subgoal unfolding extract_clvls_wl_heur_def .
  subgoal unfolding extract_ccach_wl_heur_def .
  subgoal unfolding extract_lbd_wl_heur_def .
  subgoal unfolding extract_outl_wl_heur_def .
  subgoal unfolding extract_stats_wl_heur_def .
  subgoal unfolding extract_heur_wl_heur_def .
  subgoal unfolding extract_vdom_wl_heur_def .
  subgoal unfolding extract_lcount_wl_heur_def .
  subgoal unfolding extract_opts_wl_heur_def .
  subgoal unfolding extract_old_arena_wl_heur_def .
  done

sepref_register extract_literals_to_update_wl_heur
lemmas [sepref_fr_rules] = remove_literals_to_update_wl_heur_code.refine
  remove_arena_wl_heur_code.refine [unfolded extract_arena_wl_heur_def[symmetric]]
  remove_trail_wl_heur_code.refine

(*There must some setup missing for Sepref to do that automatically*)
lemma [llvm_pre_simp]:
  \<open>(Mreturn \<circ>\<^sub>1\<^sub>6 IsaSAT_int) a1 a2 a3 x a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 =
  Mreturn (IsaSAT_int a1 a2 a3 x a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16)\<close>
  by auto

lemmas [llvm_code del] =
  update_arena_wl_heur_code_def
  update_trail_wl_heur_code_def
lemmas [llvm_code] =
  remove_literals_to_update_wl_heur_code_def
  remove_arena_wl_heur_code_def
  remove_trail_wl_heur_code_def
  bottom_decision_level_code_def
  bottom_arena_code_def
  bottom_trail_code_def
  update_arena_wl_heur_code_def[unfolded M_CONST_def,unfolded comp_def inline_node_case]
  update_trail_wl_heur_code_def[unfolded M_CONST_def,unfolded comp_def inline_node_case]



lemma add_pure_parameter:
  assumes \<open>\<And>C C'. (C, C') \<in> R \<Longrightarrow> (f C, f' C') \<in> [P C']\<^sub>a A \<rightarrow> b\<close>
  shows \<open>(uncurry f, uncurry f') \<in> [uncurry P]\<^sub>a (pure R)\<^sup>k *\<^sub>a A \<rightarrow> b\<close>
  apply sepref_to_hoare
  apply vcg
  apply auto
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv)+
  apply (rule assms[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv, rule_format])
  apply auto
  done
lemma remove_pure_parameter:
  assumes  \<open>(uncurry f, uncurry f') \<in> [uncurry P]\<^sub>a (pure R)\<^sup>k *\<^sub>a A \<rightarrow> b\<close> \<open>(C, C') \<in> R\<close>
  shows \<open>(f C, f' C') \<in> [P C']\<^sub>a A \<rightarrow> b\<close>
  using assms(2) assms(1)[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv, rule_format]
  apply sepref_to_hoare
  apply vcg
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv)+
  by (auto simp: pure_true_conv)

lemma add_pure_parameter2:
  assumes \<open>\<And>C C'. (C, C') \<in> R \<Longrightarrow> (\<lambda>S. f S C, \<lambda>S. f' S C') \<in> [\<lambda>S. P S C']\<^sub>a A \<rightarrow> b\<close>
  shows \<open>(uncurry f, uncurry f') \<in> [uncurry P]\<^sub>a A *\<^sub>a (pure R)\<^sup>k \<rightarrow> b\<close>
  apply sepref_to_hoare
  apply vcg
  apply auto
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv)+
  apply (rule assms[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv, rule_format])
  apply auto
  done

lemma remove_pure_parameter2:
  assumes  \<open>(uncurry f, uncurry f') \<in> [uncurry P]\<^sub>a A *\<^sub>a (pure R)\<^sup>k \<rightarrow> b\<close> \<open>(C, C') \<in> R\<close>
  shows \<open>(\<lambda>S. f S C, \<lambda>S. f' S C') \<in> [\<lambda>S. P  S C']\<^sub>a A \<rightarrow> b\<close>
  using assms(2) assms(1)[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv, rule_format]
  apply sepref_to_hoare
  apply vcg
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv)+
  apply (auto simp: pure_true_conv)
  done

lemma remove_pure_parameter2_twoargs:
  assumes  \<open>(uncurry2 f, uncurry2 f') \<in> [uncurry2 P]\<^sub>a A *\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure R')\<^sup>k \<rightarrow> b\<close> \<open>(C, C') \<in> R\<close> \<open>(D,D')\<in>R'\<close>
  shows \<open>(\<lambda>S. f S C D, \<lambda>S. f' S C' D') \<in> [\<lambda>S. P  S C' D']\<^sub>a A \<rightarrow> b\<close>
  using assms(2-) assms(1)[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv, rule_format]
  apply sepref_to_hoare
  apply vcg
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv)+
  apply (auto simp: pure_true_conv)
  done

(*TODO Move*)
lemma (in -) nofail_ASSERT_bind: \<open>nofail (do {ASSERT(P); (\<Phi> :: 'a nres)}) \<longleftrightarrow> P \<and> nofail \<Phi>\<close>
  by (auto simp: nofail_def ASSERT_eq iASSERT_def)

lemma refine_ASSERT_move_to_pre:
  assumes \<open>(uncurry g, uncurry h) \<in> [uncurry P]\<^sub>a A *\<^sub>a B \<rightarrow> x_assn\<close>
  shows
  \<open>(uncurry g, uncurry (\<lambda>N C. do {ASSERT (P N C); h N C}))
    \<in> A *\<^sub>a B \<rightarrow>\<^sub>a x_assn\<close>
  apply sepref_to_hoare
  apply vcg
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv)+
  apply (auto simp: nofail_ASSERT_bind)
  apply (rule assms[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv sep.add_assoc, rule_format])
  apply auto
  done

lemma refine_ASSERT_move_to_pre0:
  assumes \<open>(g, h) \<in> [P]\<^sub>a A  \<rightarrow> x_assn\<close>
  shows
  \<open>(g, (\<lambda>N. do {ASSERT (P N); h N}))
    \<in> A \<rightarrow>\<^sub>a x_assn\<close>
  apply sepref_to_hoare
  apply vcg
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv)+
  apply (auto simp: nofail_ASSERT_bind)
  apply (rule assms[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv sep.add_assoc, rule_format])
  apply auto
  done

lemma refine_ASSERT_move_to_pre2:
  assumes \<open>(uncurry2 g, uncurry2 h) \<in> [uncurry2 P]\<^sub>a A *\<^sub>a B *\<^sub>a C \<rightarrow> x_assn\<close>
  shows
  \<open>(uncurry2 g, uncurry2 (\<lambda>N C D. do {ASSERT (P N C D); h N C D}))
    \<in> A *\<^sub>a B *\<^sub>a C \<rightarrow>\<^sub>a x_assn\<close>
  apply sepref_to_hoare
  apply vcg
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv)+
  apply (auto simp: nofail_ASSERT_bind)
  apply (rule assms[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv sep.add_assoc, rule_format])
  apply auto
  done

locale read_trail_param_adder0_ops =
  fixes P :: \<open>trail_pol \<Rightarrow> bool\<close> and f' :: \<open>trail_pol \<Rightarrow> 'r nres\<close>
begin

definition mop where
  \<open>mop N = do {
    ASSERT (P (get_trail_wl_heur N));
    read_trail_wl_heur (f') N
   }\<close>

end

locale read_trail_param_adder0 = read_trail_param_adder0_ops P f'
  for P :: \<open> trail_pol \<Rightarrow> bool\<close> and f' :: \<open>trail_pol \<Rightarrow> 'r nres\<close> +
  fixes f and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close>
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a trail_pol_fast_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
lemmas refine = read_trail_wl_heur_code_refine[OF not_deleted_code_refine]


lemma mop_refine:
  \<open>((read_trail_wl_heur_code f), mop) \<in> isasat_bounded_assn\<^sup>k\<rightarrow>\<^sub>a x_assn\<close>
  unfolding mop_def
  apply (rule refine_ASSERT_move_to_pre0)
  apply (rule refine[unfolded comp_def])
  done

end


locale read_trail_param_adder =
  fixes R and f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>\<And>C C'. (C, C') \<in> R \<Longrightarrow> (f C, f' C') \<in> [P C']\<^sub>a trail_pol_fast_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
lemma refine:
  \<open>(uncurry (\<lambda>N C. read_trail_wl_heur_code (f C) N),
    uncurry (\<lambda>N C'. read_trail_wl_heur (f' C') N))
  \<in> [uncurry (\<lambda>S C. P C (get_trail_wl_heur S))]\<^sub>a isasat_bounded_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k\<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (rule read_trail_wl_heur_code_refine[OF not_deleted_code_refine, unfolded comp_def])
  apply assumption
  done
end

locale read_trail_param_adder' =
  fixes R and f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>\<And>C C'. (C, C') \<in> R \<Longrightarrow> (f C, f' C') \<in> [P C']\<^sub>a trail_pol_fast_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
lemma refine:
  \<open>(uncurry (\<lambda>C N. read_trail_wl_heur_code (f C) N),
    uncurry (\<lambda>C' N. read_trail_wl_heur (f' C') N))
  \<in> [uncurry (\<lambda>C S. P C (get_trail_wl_heur S))]\<^sub>a (pure R)\<^sup>k *\<^sub>a isasat_bounded_assn\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter)
  apply (rule read_trail_wl_heur_code_refine[OF not_deleted_code_refine, unfolded comp_def])
  apply assumption
  done
end

locale read_arena_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a arena_fast_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
lemmas refine = read_arena_wl_heur_code_refine[OF not_deleted_code_refine]
end


locale read_arena_param_adder_ops =
  fixes P :: \<open>'b \<Rightarrow> arena \<Rightarrow> bool\<close> and f' :: \<open>'b \<Rightarrow> arena_el list \<Rightarrow> 'r nres\<close>
begin

definition mop where
  \<open>mop N C = do {
    ASSERT (P C (get_clauses_wl_heur N));
    read_arena_wl_heur (f' C) N
   }\<close>

end

locale read_arena_param_adder = read_arena_param_adder_ops P f'
  for P :: \<open>'b \<Rightarrow> arena \<Rightarrow> bool\<close> and f' :: \<open>'b \<Rightarrow> arena_el list \<Rightarrow> 'r nres\<close> +
  fixes R :: \<open>('a \<times> 'b) set\<close> and f and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close>
  assumes not_deleted_code_refine: \<open>\<And>C C'. (C, C') \<in> R \<Longrightarrow> (f C, f' C') \<in> [P C']\<^sub>a arena_fast_assn\<^sup>k \<rightarrow> x_assn\<close>
begin

lemma refine:
  \<open>(uncurry (\<lambda>N C. read_arena_wl_heur_code (f C) N),
    uncurry (\<lambda>N C'. read_arena_wl_heur (f' C') N))
  \<in> [uncurry (\<lambda>S C. P C (get_clauses_wl_heur S))]\<^sub>a isasat_bounded_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k\<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (rule read_arena_wl_heur_code_refine[OF not_deleted_code_refine])
  apply assumption
  done

lemma mop_refine:
  \<open>(uncurry (\<lambda>N C. read_arena_wl_heur_code (f C) N),
    uncurry mop)
  \<in> isasat_bounded_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k\<rightarrow>\<^sub>a x_assn\<close>
  unfolding mop_def
  apply (rule refine_ASSERT_move_to_pre)
  apply (rule refine)
  done

end


lemma add_pure_parameter2_twoargs:
  assumes \<open>\<And>C C' D D'. (C, C') \<in> R \<Longrightarrow>  (D, D') \<in> R' \<Longrightarrow> (\<lambda>S. f S C D, \<lambda>S. f' S C' D') \<in> [\<lambda>S. P S C' D']\<^sub>a A \<rightarrow> b\<close>
  shows \<open>(uncurry2 f, uncurry2 f') \<in> [uncurry2 P]\<^sub>a A *\<^sub>a (pure R)\<^sup>k*\<^sub>a (pure R')\<^sup>k \<rightarrow> b\<close>
  apply sepref_to_hoare
  apply vcg
  apply auto
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv)+
  apply (rule assms[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv, rule_format])
  apply auto
  done

locale read_arena_param_adder2_twoargs =
  fixes R and R' and f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>\<And>C C' D D'. (C, C') \<in> R \<Longrightarrow> (D, D') \<in> R' \<Longrightarrow> (f C D, f' C' D') \<in> [P C' D']\<^sub>a arena_fast_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
lemma refine:
  \<open>(uncurry2 (\<lambda>N C D. read_arena_wl_heur_code (f C D) N),
    uncurry2 (\<lambda>N C' D. read_arena_wl_heur (f' C' D) N))
  \<in> [uncurry2 (\<lambda>S C D. P C D (get_clauses_wl_heur S))]\<^sub>a isasat_bounded_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure R')\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2_twoargs)
  apply (rule read_arena_wl_heur_code_refine[OF not_deleted_code_refine])
  apply assumption+
  done
end

locale read_arena_param_adder2_twoargs'_ops =
  fixes
    f' :: \<open>arena_el list \<Rightarrow> 'b \<Rightarrow> 'd \<Rightarrow> 'r nres\<close> and
    P :: \<open>'b \<Rightarrow> 'd \<Rightarrow> arena_el list \<Rightarrow> bool\<close>
begin
definition mop where
  \<open>mop N C C' = do {
     ASSERT (P C C' (get_clauses_wl_heur N));
     read_arena_wl_heur (\<lambda>N. f' N C C') N
  }\<close>
end

locale read_arena_param_adder2_twoargs' = read_arena_param_adder2_twoargs'_ops f' P
  for
    f' :: \<open>arena_el list \<Rightarrow> 'b \<Rightarrow> 'd \<Rightarrow> 'r nres\<close> and
    P :: \<open>'b \<Rightarrow> 'd \<Rightarrow> arena_el list \<Rightarrow> bool\<close> +
  fixes R :: \<open>('a \<times> 'b) set\<close> and R' :: \<open>('c \<times> 'd) set\<close> and
    f :: \<open>64 word \<times> 64 word \<times> 32 word ptr \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> 'q llM\<close> and
    x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close>
  assumes not_deleted_code_refine: \<open>\<And>C C' D D'. (C, C') \<in> R \<Longrightarrow> (D, D') \<in> R' \<Longrightarrow> (\<lambda>S. f S C D, \<lambda>S. f' S C' D') \<in> [P C' D']\<^sub>a arena_fast_assn\<^sup>k \<rightarrow> x_assn\<close>
begin

lemma refine:
  \<open>(uncurry2 (\<lambda>N C D. read_arena_wl_heur_code (\<lambda>N. f N C D) N),
    uncurry2 (\<lambda>N C' D. read_arena_wl_heur (\<lambda>N. f' N C' D) N))
  \<in> [uncurry2 (\<lambda>S C D. P C D (get_clauses_wl_heur S))]\<^sub>a isasat_bounded_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure R')\<^sup>k \<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2_twoargs)
  apply (rule read_arena_wl_heur_code_refine[OF not_deleted_code_refine])
  apply assumption+
  done

lemma mop_refine:
  \<open>(uncurry2 (\<lambda>N C D. read_arena_wl_heur_code (\<lambda>N. f N C D) N), uncurry2 mop) \<in> isasat_bounded_assn\<^sup>k *\<^sub>a (pure R)\<^sup>k *\<^sub>a (pure R')\<^sup>k \<rightarrow>\<^sub>a x_assn\<close>
  unfolding mop_def
  apply (rule refine_ASSERT_move_to_pre2)
  apply (rule refine[unfolded comp_def])
  done
end


locale read_conflict_param_adder =
  fixes R and f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>\<And>C C'. (C, C') \<in> R \<Longrightarrow> (f C, f' C') \<in> [P C']\<^sub>a conflict_option_rel_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
lemma refine:
  \<open>(uncurry (\<lambda>N C. read_conflict_wl_heur_code (f C) N),
    uncurry (\<lambda>N C'. read_conflict_wl_heur (f' C') N))
  \<in> [uncurry (\<lambda>S C. P C (get_conflict_wl_heur S))]\<^sub>a isasat_bounded_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k\<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (rule read_conflict_wl_heur_code_refine[OF not_deleted_code_refine])
  apply assumption
  done
end


lemma add_pure_parameter_unit:
  assumes \<open>(\<lambda>S. f S (), \<lambda>S. f' S ()) \<in> [\<lambda>S. P S]\<^sub>a A \<rightarrow> b\<close>
  shows \<open>(f (), f' ()) \<in> [P]\<^sub>a A \<rightarrow> b\<close>
  apply sepref_to_hoare
  apply vcg
  apply (subst POSTCOND_def hn_ctxt_def sep_conj_empty' pure_true_conv)+
  apply (rule assms[to_hnr, simplified, unfolded hn_ctxt_def hn_refine_def htriple_def
    sep_conj_empty' pure_true_conv, rule_format])
  apply auto
  done

locale read_conflict_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a conflict_option_rel_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
lemmas refine = read_conflict_wl_heur_code_refine[OF not_deleted_code_refine]
end

locale read_watchlist_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a watchlist_fast_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
lemmas refine = read_watchlist_wl_heur_code_refine[OF not_deleted_code_refine]
end

locale read_vmtf_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a vmtf_remove_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
lemmas refine = read_vmtf_wl_heur_code_refine[OF not_deleted_code_refine]
end

locale read_count_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a lcount_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
lemmas refine = read_lcount_wl_heur_code_refine[OF not_deleted_code_refine]
end

locale read_ccach_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a cach_refinement_l_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
lemmas refine = read_ccach_wl_heur_code_refine[OF not_deleted_code_refine]
end

locale read_clvls_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
lemmas refine = read_clvls_wl_heur_code_refine[OF not_deleted_code_refine]
end

locale read_lbd_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a lbd_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
lemmas refine = read_lbd_wl_heur_code_refine[OF not_deleted_code_refine]
end

locale read_outl_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a out_learned_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
lemmas refine = read_outl_wl_heur_code_refine[OF not_deleted_code_refine]
end

locale read_stats_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a stats_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
lemmas refine = read_stats_wl_heur_code_refine[OF not_deleted_code_refine]
end

locale read_heur_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a heuristic_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
lemmas refine = read_heur_wl_heur_code_refine[OF not_deleted_code_refine]
end

locale read_vdom_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a aivdom_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
lemmas refine = read_vdom_wl_heur_code_refine[OF not_deleted_code_refine]
end

locale read_vdom_param_adder =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P and C and C' and R
  assumes not_deleted_code_refine: \<open>\<And>C C'. (C, C') \<in> R \<Longrightarrow> (f C, f' C') \<in> [P C']\<^sub>a aivdom_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
lemma refine:
  \<open>(uncurry (\<lambda>N C. read_vdom_wl_heur_code (f C) N),
    uncurry (\<lambda>N C'. read_vdom_wl_heur (f' C') N))
  \<in> [uncurry (\<lambda>S C. P C (get_aivdom S))]\<^sub>a isasat_bounded_assn\<^sup>k  *\<^sub>a (pure R)\<^sup>k\<rightarrow> x_assn\<close>
  apply (rule add_pure_parameter2)
  apply (rule read_vdom_wl_heur_code_refine[OF not_deleted_code_refine, unfolded comp_def])
  apply assumption
  done

end


locale read_lcount_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a lcount_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
lemmas refine = read_lcount_wl_heur_code_refine[OF not_deleted_code_refine]
end

locale read_opts_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a opts_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
lemmas refine = read_opts_wl_heur_code_refine[OF not_deleted_code_refine]
end

locale read_old_arena_param_adder0 =
  fixes f and f' and x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and P
  assumes not_deleted_code_refine: \<open>(f, f') \<in> [P]\<^sub>a arena_fast_assn\<^sup>k \<rightarrow> x_assn\<close>
begin
lemmas refine = read_old_arena_wl_heur_code_refine[OF not_deleted_code_refine]
end


lemma Mreturn_comp_IsaSAT_int:
  \<open>(Mreturn o\<^sub>1\<^sub>6 IsaSAT_int) a b c d e f g h i j k l m n ko p =
  Mreturn (IsaSAT_int a b c d e f g h i j k l m n ko p)\<close>
  by auto

lemmas [sepref_fr_rules] = remove_lcount_wl_heur_code.refine update_lcount_wl_heur_code.refine
lemmas [unfolded inline_direct_return_node_case, llvm_code] =
  extract_lcount_wl_heur_def[unfolded isasat_state_ops.remove_lcount_wl_heur_def]
  extract_vdom_wl_heur_def[unfolded isasat_state_ops.remove_vdom_wl_heur_def]
  remove_lcount_wl_heur_code_def[unfolded Mreturn_comp_IsaSAT_int]
  remove_vdom_wl_heur_code_def[unfolded Mreturn_comp_IsaSAT_int]

sepref_register remove_heur_wl_heur
lemmas [sepref_fr_rules] =
  remove_trail_wl_heur_code.refine
  remove_arena_wl_heur_code.refine
  remove_conflict_wl_heur_code.refine
  remove_literals_to_update_wl_heur_code.refine
  remove_vmtf_wl_heur_code.refine
  remove_clvls_wl_heur_code.refine
  remove_ccach_wl_heur_code.refine

  remove_vdom_wl_heur_code.refine
  remove_lcount_wl_heur_code.refine
  remove_outl_wl_heur_code.refine
  remove_heur_wl_heur_code.refine
  remove_stats_wl_heur_code.refine
  remove_opts_wl_heur_code.refine
  remove_old_arena_wl_heur_code.refine
  remove_lbd_wl_heur_code.refine
  remove_old_arena_wl_heur_code.refine


lemma lambda_comp_true: \<open>(\<lambda>S. True) \<circ> f = (\<lambda>_. True)\<close> \<open>uncurry (\<lambda>a b. True) = (\<lambda>_. True)\<close>  \<open>uncurry2 (\<lambda>a b c. True) = (\<lambda>_. True)\<close>
  by auto

named_theorems state_extractors \<open>Definition of all functions modifying the state\<close>
lemmas [state_extractors] =
  extract_trail_wl_heur_def
  extract_arena_wl_heur_def
  extract_conflict_wl_heur_def
  extract_watchlist_wl_heur_def
  extract_stats_wl_heur_def
  extract_heur_wl_heur_def
  extract_lcount_wl_heur_def
  isasat_state_ops.remove_trail_wl_heur_def
  isasat_state_ops.remove_arena_wl_heur_def
  isasat_state_ops.remove_conflict_wl_heur_def
  isasat_state_ops.remove_watchlist_wl_heur_def
  isasat_state_ops.remove_stats_wl_heur_def
  isasat_state_ops.remove_heur_wl_heur_def
  isasat_state_ops.remove_lcount_wl_heur_def
  update_trail_wl_heur_def
  update_arena_wl_heur_def
  update_conflict_wl_heur_def
  update_watchlist_wl_heur_def
  update_stats_wl_heur_def
  update_heur_wl_heur_def
  update_lcount_wl_heur_def

end
