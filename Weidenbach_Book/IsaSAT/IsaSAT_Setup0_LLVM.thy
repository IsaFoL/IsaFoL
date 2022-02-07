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

datatype ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) isasat_int = IsaSAT_int
  (get_trail_wl_heur: 'a)
  (get_clauses_wl_heur: 'b)
  (get_conflict_wl_heur: 'c)
  (literals_to_update_wl_heur: 'd)
  (get_watched_wl_heur: 'e)
  (get_vmtf_heur: 'f)
  (get_count_max_lvls_heur: 'g)
  (get_conflict_cach: 'h)
  (get_lbd: 'i)
  (get_outlearned_heur: 'j)
  (get_heur: 'k)
  (get_stats_heur: 'l)
  (get_aivdom: 'm)
  (get_learned_count: 'n)
  (get_opts: 'o)
  (get_old_arena: 'p)

instantiation isasat_int ::
  (llvm_rep,llvm_rep,llvm_rep,llvm_rep,
  llvm_rep,llvm_rep,llvm_rep,llvm_rep,
  llvm_rep,llvm_rep,llvm_rep,llvm_rep,
  llvm_rep,llvm_rep,llvm_rep,llvm_rep) llvm_rep
begin
  definition to_val_isasat_int where
    \<open>to_val_isasat_int \<equiv> (\<lambda>S. case S of
     IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena \<Rightarrow> LL_STRUCT [to_val M, to_val N, to_val D, to_val i, to_val W, to_val ivmtf,
       to_val icount, to_val ccach, to_val lbd,
       to_val outl, to_val heur, to_val stats, to_val aivdom,  to_val clss, to_val opts, to_val arena])\<close>

  definition from_val_isasat_int :: \<open>llvm_val \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
    \<open>from_val_isasat_int \<equiv> (\<lambda>p. case llvm_val.the_fields p of
   [M, N, D, i, W, ivmtf, icount, ccach, lbd, outl, heur, stats, aivdom, clss, opts, arena] \<Rightarrow>
     IsaSAT_int (from_val M) (from_val N) (from_val D) (from_val i) (from_val W) (from_val ivmtf) (from_val icount) (from_val ccach) (from_val lbd)
       (from_val outl) (from_val heur) (from_val stats) (from_val aivdom) (from_val clss) (from_val opts) (from_val arena))\<close>

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
  to_val (get_heur x),
  to_val (get_stats_heur x),
  to_val (get_aivdom x),
  to_val (get_learned_count x),
  to_val (get_opts x),
  to_val (get_old_arena x)]"
  apply (cases x)
  apply (auto simp: to_val_isasat_int_def)
  done

lemma node_insert_value:
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) M' 0 = Mreturn (IsaSAT_int M' N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) N' (Suc 0) = Mreturn (IsaSAT_int M N' D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) D' 2 = Mreturn (IsaSAT_int M N D' i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) i' 3 = Mreturn (IsaSAT_int M N D i' W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) W' 4 = Mreturn (IsaSAT_int M N D i W' ivmtf icount ccach lbd outl heur stats aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) ivmtf' 5 = Mreturn (IsaSAT_int M N D i W ivmtf' icount ccach lbd outl heur stats aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) icount' 6 = Mreturn (IsaSAT_int M N D i W ivmtf icount' ccach lbd outl heur stats aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) ccach' 7 = Mreturn (IsaSAT_int M N D i W ivmtf icount ccach' lbd outl heur stats aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) lbd' 8 = Mreturn (IsaSAT_int M N D i W ivmtf icount ccach lbd' outl heur stats aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) outl' 9 = Mreturn (IsaSAT_int M N D i W ivmtf icount ccach lbd outl' heur stats aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) heur' 10 = Mreturn (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur' stats aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) stats' 11 = Mreturn (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats' aivdom clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) aivdom' 12 = Mreturn (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom' clss opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) clss' 13 = Mreturn (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss' opts arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) opts' 14 = Mreturn (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts' arena)"
  "ll_insert_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) arena' 15 = Mreturn (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena')"
  by (simp_all add: ll_insert_value_def llvm_insert_value_def Let_def checked_from_val_def
                to_val_isasat_int_def from_val_isasat_int_def)

lemma node_extract_value:
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) 0 = Mreturn M"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) (Suc 0) = Mreturn N"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) 2 = Mreturn D"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) 3 = Mreturn i"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) 4 = Mreturn W"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) 5 = Mreturn ivmtf"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) 6 = Mreturn icount"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) 7 = Mreturn ccach"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) 8 = Mreturn lbd"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) 9 = Mreturn outl"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) 10 = Mreturn heur"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) 11 = Mreturn stats"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) 12 = Mreturn aivdom"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) 13 = Mreturn clss"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) 14 = Mreturn opts"
  "ll_extract_value (IsaSAT_int M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena) 15 = Mreturn arena"
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

  term from_val
  term uint64_nat_assn
  term ll_bpto
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

definition test where
  \<open>test M = isasat_int.literals_to_update_wl_heur M\<close>



definition isasat_bounded_assn :: \<open>_ \<Rightarrow> _ \<Rightarrow> assn\<close> where
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
sepref_def test_impl
  is \<open>RETURN o test\<close>
  :: \<open>isasat_bounded_assn\<^sup>k \<rightarrow>\<^sub>a sint64_nat_assn\<close>
  unfolding test_def
  by sepref
export_llvm test_impl


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
    a :: \<open>unit \<Rightarrow> 'xa llM\<close> and
    b_default :: 'b and
    b :: \<open>unit \<Rightarrow> 'xb llM\<close> and
    c_default :: 'c and
    c :: \<open>unit \<Rightarrow> 'xc llM\<close> and
    d_default :: 'd and
    d :: \<open>unit \<Rightarrow> 'xd llM\<close> and
    e_default :: 'e and
    e :: \<open>unit \<Rightarrow> 'xe llM\<close> and
    f_default :: 'f and
    f :: \<open>unit \<Rightarrow> 'xf llM\<close> and
    g_default :: 'g and
    g :: \<open>unit \<Rightarrow> 'xg llM\<close> and
    h_default :: 'h and
    h :: \<open>unit \<Rightarrow> 'xh llM\<close> and
    i_default :: 'i and
    i :: \<open>unit \<Rightarrow> 'xi llM\<close> and
    j_default :: 'j and
    j :: \<open>unit \<Rightarrow> 'xj llM\<close> and
    k_default :: 'k and
    k :: \<open>unit \<Rightarrow> 'xk llM\<close> and
    l_default :: 'l and
    l :: \<open>unit \<Rightarrow> 'xl llM\<close> and
    m_default :: 'm and
    m :: \<open>unit \<Rightarrow> 'xm llM\<close> and
    n_default :: 'n and
    n :: \<open>unit \<Rightarrow> 'xn llM\<close> and
    ko_default :: 'o and
    ko :: \<open>unit \<Rightarrow> 'xo llM\<close> and
    p_default :: 'p and
    p :: \<open>unit \<Rightarrow> 'xp llM\<close>
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


definition remove_trail_wl_heur_int :: \<open>('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int \<Rightarrow> ('xa \<times> ('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int, _) M\<close> where
  \<open>remove_trail_wl_heur_int isasat_int =
    (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
     doM{
    a' \<leftarrow> a ();
    S \<leftarrow> Mreturn (IsaSAT_int a' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16);
    Mreturn (x1, S)
  })\<close>

definition remove_arena_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'b \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_arena_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x2, IsaSAT_int x1 b_default x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16))\<close>


definition remove_arena_wl_heur_int :: \<open>('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int \<Rightarrow> ('xb \<times> ('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int, _) M\<close> where
  \<open>remove_arena_wl_heur_int isasat_int =
    (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
     doM{
    a' \<leftarrow> b ();
    S \<leftarrow> Mreturn (IsaSAT_int x1 a' x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16);
    Mreturn (x2, S)
  })\<close>

definition remove_conflict_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _ \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_conflict_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x3, IsaSAT_int x1 x2 c_default x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16))\<close>


definition remove_conflict_wl_heur_int :: \<open>('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int \<Rightarrow> ('xc \<times> ('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int, _) M\<close> where
  \<open>remove_conflict_wl_heur_int isasat_int =
    (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
     doM{
    a' \<leftarrow> c ();
    S \<leftarrow> Mreturn (IsaSAT_int x1 x2 a' x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16);
    Mreturn (x3, S)
  })\<close>

definition remove_literals_to_update_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> _ \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_literals_to_update_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x4, IsaSAT_int x1 x2 x3 d_default x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16))\<close>


definition remove_literals_to_update_wl_heur_int :: \<open>('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int \<Rightarrow> ('xd \<times> ('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int, _) M\<close> where
  \<open>remove_literals_to_update_wl_heur_int isasat_int =
    (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
     doM{
    d' \<leftarrow> d ();
    S \<leftarrow> Mreturn (IsaSAT_int x1 x2 x3 d' x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16);
    Mreturn (x4, S)
  })\<close>

definition remove_watchlist_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'e \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_watchlist_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x5, IsaSAT_int x1 x2 x3 x4 e_default x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16))\<close>


definition remove_watchlist_wl_heur_int :: \<open>('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int \<Rightarrow> ('xe \<times> ('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int, _) M\<close> where
  \<open>remove_watchlist_wl_heur_int isasat_int =
    (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
     doM{
    a' \<leftarrow> e ();
    S \<leftarrow> Mreturn (IsaSAT_int x1 x2 x3 x4 a' x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16);
    Mreturn (x5, S)
  })\<close>

definition remove_vmtf_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'f \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_vmtf_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x6, IsaSAT_int x1 x2 x3 x4 x5 f_default x7 x8 x9 x10 x11 x12 x13 x14 x15 x16))\<close>

definition remove_vmtf_wl_heur_int :: \<open>('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int \<Rightarrow> ('xf \<times> ('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int, _) M\<close> where
  \<open>remove_vmtf_wl_heur_int isasat_int =
    (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
     doM{
    a' \<leftarrow> f ();
    S \<leftarrow> Mreturn (IsaSAT_int x1 x2 x3 x4 x5 a' x7 x8 x9 x10 x11 x12 x13 x14 x15 x16);
    Mreturn (x6, S)
  })\<close>


definition remove_clvls_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'g \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_clvls_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x7, IsaSAT_int x1 x2 x3 x4 x5 x6 g_default x8 x9 x10 x11 x12 x13 x14 x15 x16))\<close>

definition remove_clvls_wl_heur_int :: \<open>('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int \<Rightarrow> ('xg \<times> ('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int, _) M\<close> where
  \<open>remove_clvls_wl_heur_int isasat_int =
    (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
     doM{
    a' \<leftarrow> g ();
    S \<leftarrow> Mreturn (IsaSAT_int x1 x2 x3 x4 x5 x6 a' x8 x9 x10 x11 x12 x13 x14 x15 x16);
    Mreturn (x7, S)
  })\<close>

definition remove_ccach_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'h \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_ccach_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x8, IsaSAT_int x1 x2 x3 x4 x5 x6 x7 h_default x9 x10 x11 x12 x13 x14 x15 x16))\<close>

definition remove_ccach_wl_heur_int :: \<open>('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int \<Rightarrow> ('xh \<times> ('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int, _) M\<close> where
  \<open>remove_ccach_wl_heur_int isasat_int =
    (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
     doM{
    a' \<leftarrow> h ();
    S \<leftarrow> Mreturn (IsaSAT_int x1 x2 x3 x4 x5 x6 x7 a' x9 x10 x11 x12 x13 x14 x15 x16);
    Mreturn (x8, S)
  })\<close>

definition remove_lbd_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'i \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_lbd_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x9, IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 i_default x10 x11 x12 x13 x14 x15 x16))\<close>

definition remove_lbd_wl_heur_int :: \<open>('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int \<Rightarrow> ('xi \<times> ('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int, _) M\<close> where
  \<open>remove_lbd_wl_heur_int isasat_int =
    (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
     doM{
    a' \<leftarrow> i ();
    S \<leftarrow> Mreturn (IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 a' x10 x11 x12 x13 x14 x15 x16);
    Mreturn (x9, S)
  })\<close>

definition remove_outl_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'j \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_outl_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x10, IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 j_default x11 x12 x13 x14 x15 x16))\<close>

definition remove_outl_wl_heur_int :: \<open>('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int \<Rightarrow> ('xj \<times> ('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int, _) M\<close> where
  \<open>remove_outl_wl_heur_int isasat_int =
    (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
     doM{
    a' \<leftarrow> j ();
    S \<leftarrow> Mreturn (IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 a' x11 x12 x13 x14 x15 x16);
    Mreturn (x10, S)
  })\<close>

definition remove_stats_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'k \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_stats_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x11, IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 k_default x12 x13 x14 x15 x16))\<close>

definition remove_stats_wl_heur_int :: \<open>('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int \<Rightarrow> ('xk \<times> ('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int, _) M\<close> where
  \<open>remove_stats_wl_heur_int isasat_int =
    (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
     doM{
    a' \<leftarrow> k ();
    S \<leftarrow> Mreturn (IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 a' x12 x13 x14 x15 x16);
    Mreturn (x11, S)
  })\<close>

definition remove_heur_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'l \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_heur_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x12, IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 l_default x13 x14 x15 x16))\<close>

definition remove_heur_wl_heur_int :: \<open>('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int \<Rightarrow> ('xl \<times> ('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int, _) M\<close> where
  \<open>remove_heur_wl_heur_int isasat_int =
    (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
     doM{
    a' \<leftarrow> l ();
    S \<leftarrow> Mreturn (IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 a' x13 x14 x15 x16);
    Mreturn (x12, S)
  })\<close>
definition remove_vdom_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'm \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_vdom_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x13, IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 m_default x14 x15 x16))\<close>

definition remove_vdom_wl_heur_int :: \<open>('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int \<Rightarrow> ('xm \<times> ('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int, _) M\<close> where
  \<open>remove_vdom_wl_heur_int isasat_int =
    (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
     doM{
    a' \<leftarrow> m ();
    S \<leftarrow> Mreturn (IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 a' x14 x15 x16);
    Mreturn (x13, S)
  })\<close>

definition remove_lcount_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'n \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_lcount_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x14, IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 n_default x15 x16))\<close>

definition remove_lcount_wl_heur_int :: \<open>('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int \<Rightarrow> ('xn \<times> ('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int, _) M\<close> where
  \<open>remove_lcount_wl_heur_int isasat_int =
    (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
     doM{
    a' \<leftarrow> n ();
    S \<leftarrow> Mreturn (IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 a' x15 x16);
    Mreturn (x14, S)
  })\<close>

definition remove_opts_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'o \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_opts_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x15, IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ko_default x16))\<close>

definition remove_opts_wl_heur_int :: \<open>('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int \<Rightarrow> ('xo \<times> ('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int, _) M\<close> where
  \<open>remove_opts_wl_heur_int isasat_int =
    (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
     doM{
    a' \<leftarrow> ko ();
    S \<leftarrow> Mreturn (IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 a' x16);
    Mreturn (x15, S)
  })\<close>


definition remove_old_arena_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int \<Rightarrow> 'p \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p) isasat_int\<close> where
  \<open>remove_old_arena_wl_heur isasat_int = (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
      (x16, IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 p_default))\<close>

definition remove_old_arena_wl_heur_int :: \<open>('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int \<Rightarrow> ('xp \<times> ('xa, 'xb, 'xc, 'xd, 'xe, 'xf, 'xg, 'xh, 'xi, 'xj,
     'xk, 'xl, 'xm, 'xn, 'xo, 'xp) isasat_int, _) M\<close> where
  \<open>remove_old_arena_wl_heur_int isasat_int =
    (case isasat_int of IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 \<Rightarrow>
     doM{
    a' \<leftarrow> p ();
    S \<leftarrow> Mreturn (IsaSAT_int x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 a');
    Mreturn (x16, S)
  })\<close>
end



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
    a :: \<open>unit \<Rightarrow> 'xa llM\<close> and
    b_default :: 'b and
    b :: \<open>unit \<Rightarrow> 'xb llM\<close> and
    c_default :: 'c and
    c :: \<open>unit \<Rightarrow> 'xc llM\<close> and
    d_default :: 'd and
    d :: \<open>unit \<Rightarrow> 'xd llM\<close> and
    e_default :: 'e and
    e :: \<open>unit \<Rightarrow> 'xe llM\<close> and
    f_default :: 'f and
    f :: \<open>unit \<Rightarrow> 'xf llM\<close> and
    g_default :: 'g and
    g :: \<open>unit \<Rightarrow> 'xg llM\<close> and
    h_default :: 'h and
    h :: \<open>unit \<Rightarrow> 'xh llM\<close> and
    i_default :: 'i and
    i :: \<open>unit \<Rightarrow> 'xi llM\<close> and
    j_default :: 'j and
    j :: \<open>unit \<Rightarrow> 'xj llM\<close> and
    k_default :: 'k and
    k :: \<open>unit \<Rightarrow> 'xk llM\<close> and
    l_default :: 'l and
    l :: \<open>unit \<Rightarrow> 'xl llM\<close> and
    m_default :: 'm and
    m :: \<open>unit \<Rightarrow> 'xm llM\<close> and
    n_default :: 'n and
    n :: \<open>unit \<Rightarrow> 'xn llM\<close> and
    ko_default :: 'o and
    ko :: \<open>unit \<Rightarrow> 'xo llM\<close> and
    p_default :: 'p and
    p :: \<open>unit \<Rightarrow> 'xp llM\<close> +
  assumes
    a: \<open>(a, uncurry0 (RETURN a_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a a_assn\<close> and
    b: \<open>(b, uncurry0 (RETURN b_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a b_assn\<close> and
    c: \<open>(c, uncurry0 (RETURN c_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a c_assn\<close> and
    d: \<open>(d, uncurry0 (RETURN d_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a d_assn\<close> and
    e: \<open>(e, uncurry0 (RETURN e_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a e_assn\<close> and
    f: \<open>(f, uncurry0 (RETURN f_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a f_assn\<close> and
    g: \<open>(g, uncurry0 (RETURN g_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a g_assn\<close> and
    h: \<open>(h, uncurry0 (RETURN h_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a h_assn\<close> and
    i: \<open>(i, uncurry0 (RETURN i_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a i_assn\<close> and
    j: \<open>(j, uncurry0 (RETURN j_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a j_assn\<close> and
    k: \<open>(k, uncurry0 (RETURN k_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a k_assn\<close> and
    l: \<open>(l, uncurry0 (RETURN l_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a l_assn\<close> and
    m: \<open>(m, uncurry0 (RETURN m_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a m_assn\<close> and
    n: \<open>(n, uncurry0 (RETURN n_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a n_assn\<close> and
    o: \<open>(ko, uncurry0 (RETURN ko_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a o_assn\<close>and
    p: \<open>(p, uncurry0 (RETURN p_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a p_assn\<close>
begin

lemma ex_isasat_int_iff: "(\<exists>b :: (_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_)isasat_int. P b) \<longleftrightarrow>
  (\<exists>a b  c d e f g h i j k l m n ko p. P (IsaSAT_int a b  c d e f g h i j k l m n ko p))"
  apply auto
    apply (case_tac b)
  by force


lemma remove_trail_wl_heur_int:
  \<open>(remove_trail_wl_heur_int, RETURN o remove_trail_wl_heur) \<in> isasat_assn\<^sup>d \<rightarrow>\<^sub>a a_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_trail_wl_heur_int_def remove_trail_wl_heur_def isasat_assn_def
  supply [split] =  isasat_int.splits
  apply sepref_to_hoare
  apply (case_tac x)
  apply vcg
  unfolding wpa_return
  apply (subst (asm)(2) sep_algebra_class.sep_conj_empty'[symmetric])
  apply (rule apply_htriple_rule)
  apply assumption
  apply (rule a[to_hnr, simplified, unfolded hn_refine_def, rule_format])
  apply (solves auto)
  apply (rule POSTCONDI)
  apply (rule STATE_monoI)
  apply assumption
  subgoal premises p for x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x1a x2a x3a x4a x5a x6a x7a x8a x9a x10a x11a x12a x13a x14a x15a x16a asf s s' r
    unfolding ex_isasat_int_iff entails_def
    apply (auto simp: Exists_eq_simp ex_isasat_int_iff  entails_def entails_eq_iff pure_true_conv sep_conj_left_commute)
    by (smt (z3) entails_def entails_eq_iff pure_true_conv sep_conj_aci(4) sep_conj_aci(5) sep_conj_left_commute )
  done


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

lemma remove_arena_wl_heur_int:
  \<open>(remove_arena_wl_heur_int, RETURN o remove_arena_wl_heur) \<in> isasat_assn\<^sup>d \<rightarrow>\<^sub>a b_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_arena_wl_heur_int_def remove_arena_wl_heur_def isasat_assn_def
  supply [split] = isasat_int.splits
  apply stuff_pre
  apply assumption
  apply (rule b[to_hnr, simplified, unfolded hn_refine_def, rule_format])
  apply (solves auto)
  apply (stuff_post1)
  apply assumption
  apply (stuff_post2)
  done

lemma remove_conflict_wl_heur_int:
  \<open>(remove_conflict_wl_heur_int, RETURN o remove_conflict_wl_heur) \<in> isasat_assn\<^sup>d \<rightarrow>\<^sub>a c_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_conflict_wl_heur_int_def remove_conflict_wl_heur_def isasat_assn_def
  supply [split] =  isasat_int.splits
  apply stuff_pre
  apply assumption
  apply (rule c[to_hnr, simplified, unfolded hn_refine_def, rule_format])
  apply (solves auto)
  apply (stuff_post1)
  apply assumption
  apply (stuff_post2)
  done

lemma remove_literals_to_update_wl_heur_int:
  \<open>(remove_literals_to_update_wl_heur_int, RETURN o remove_literals_to_update_wl_heur) \<in> isasat_assn\<^sup>d \<rightarrow>\<^sub>a d_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_literals_to_update_wl_heur_int_def remove_literals_to_update_wl_heur_def isasat_assn_def
  supply [split] =  isasat_int.splits
  apply stuff_pre
  apply assumption
  apply (rule d[to_hnr, simplified, unfolded hn_refine_def, rule_format])
  apply (solves auto)
  apply (stuff_post1)
  apply assumption
  apply (stuff_post2)
  done

lemma remove_watchlist_wl_heur_int:
  \<open>(remove_watchlist_wl_heur_int, RETURN o remove_watchlist_wl_heur) \<in> isasat_assn\<^sup>d \<rightarrow>\<^sub>a e_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_watchlist_wl_heur_int_def remove_watchlist_wl_heur_def isasat_assn_def
  supply [split] =  isasat_int.splits
  apply stuff_pre
  apply assumption
  apply (rule e[to_hnr, simplified, unfolded hn_refine_def, rule_format])
  apply (solves auto)
  apply (stuff_post1)
  apply assumption
  apply (stuff_post2)
  done

lemma remove_vmtf_wl_heur_int:
  \<open>(remove_vmtf_wl_heur_int, RETURN o remove_vmtf_wl_heur) \<in> isasat_assn\<^sup>d \<rightarrow>\<^sub>a f_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_vmtf_wl_heur_int_def remove_vmtf_wl_heur_def isasat_assn_def
  supply [split] =  isasat_int.splits
  apply stuff_pre
  apply assumption
  apply (rule f[to_hnr, simplified, unfolded hn_refine_def, rule_format])
  apply (solves auto)
  apply (stuff_post1)
  apply assumption
  apply (stuff_post2)
  done

lemma remove_clvls_wl_heur_int:
  \<open>(remove_clvls_wl_heur_int, RETURN o remove_clvls_wl_heur) \<in> isasat_assn\<^sup>d \<rightarrow>\<^sub>a g_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_clvls_wl_heur_int_def remove_clvls_wl_heur_def isasat_assn_def
  supply [split] =  isasat_int.splits
  apply stuff_pre
  apply assumption
  apply (rule g[to_hnr, simplified, unfolded hn_refine_def, rule_format])
  apply (solves auto)
  apply (stuff_post1)
  apply assumption
  apply (stuff_post2)
  done

lemma remove_ccach_wl_heur_int:
  \<open>(remove_ccach_wl_heur_int, RETURN o remove_ccach_wl_heur) \<in> isasat_assn\<^sup>d \<rightarrow>\<^sub>a h_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_ccach_wl_heur_int_def remove_ccach_wl_heur_def isasat_assn_def
  supply [split] =  isasat_int.splits
  apply stuff_pre
  apply assumption
  apply (rule h[to_hnr, simplified, unfolded hn_refine_def, rule_format])
  apply (solves auto)
  apply (stuff_post1)
  apply assumption
  apply (stuff_post2)
  done

lemma remove_lbd_wl_heur_int:
  \<open>(remove_lbd_wl_heur_int, RETURN o remove_lbd_wl_heur) \<in> isasat_assn\<^sup>d \<rightarrow>\<^sub>a i_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_lbd_wl_heur_int_def remove_lbd_wl_heur_def isasat_assn_def
  supply [split] =  isasat_int.splits
  apply stuff_pre
  apply assumption
  apply (rule i[to_hnr, simplified, unfolded hn_refine_def, rule_format])
  apply (solves auto)
  apply (stuff_post1)
  apply assumption
  apply (stuff_post2)
  done

lemma remove_outl_wl_heur_int:
  \<open>(remove_outl_wl_heur_int, RETURN o remove_outl_wl_heur) \<in> isasat_assn\<^sup>d \<rightarrow>\<^sub>a j_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_outl_wl_heur_int_def remove_outl_wl_heur_def isasat_assn_def
  supply [split] =  isasat_int.splits
  apply stuff_pre
  apply assumption
  apply (rule j[to_hnr, simplified, unfolded hn_refine_def, rule_format])
  apply (solves auto)
  apply (stuff_post1)
  apply assumption
  apply (stuff_post2)
  done

lemma remove_stats_wl_heur_int:
  \<open>(remove_stats_wl_heur_int, RETURN o remove_stats_wl_heur) \<in> isasat_assn\<^sup>d \<rightarrow>\<^sub>a k_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_stats_wl_heur_int_def remove_stats_wl_heur_def isasat_assn_def
  supply [split] =  isasat_int.splits
  apply stuff_pre
  apply assumption
  apply (rule k[to_hnr, simplified, unfolded hn_refine_def, rule_format])
  apply (solves auto)
  apply (stuff_post1)
  apply assumption
  apply (stuff_post2)
  done

lemma remove_heur_wl_heur_int:
  \<open>(remove_heur_wl_heur_int, RETURN o remove_heur_wl_heur) \<in> isasat_assn\<^sup>d \<rightarrow>\<^sub>a l_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_heur_wl_heur_int_def remove_heur_wl_heur_def isasat_assn_def
  supply [split] =  isasat_int.splits
  apply stuff_pre
  apply assumption
  apply (rule l[to_hnr, simplified, unfolded hn_refine_def, rule_format])
  apply (solves auto)
  apply (stuff_post1)
  apply assumption
  apply (stuff_post2)
  done

lemma remove_vdom_wl_heur_int:
  \<open>(remove_vdom_wl_heur_int, RETURN o remove_vdom_wl_heur) \<in> isasat_assn\<^sup>d \<rightarrow>\<^sub>a m_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_vdom_wl_heur_int_def remove_vdom_wl_heur_def isasat_assn_def
  supply [split] =  isasat_int.splits
  apply stuff_pre
  apply assumption
  apply (rule m[to_hnr, simplified, unfolded hn_refine_def, rule_format])
  apply (solves auto)
  apply (stuff_post1)
  apply assumption
  apply (stuff_post2)
  done

lemma remove_lcount_wl_heur_int:
  \<open>(remove_lcount_wl_heur_int, RETURN o remove_lcount_wl_heur) \<in> isasat_assn\<^sup>d \<rightarrow>\<^sub>a n_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_lcount_wl_heur_int_def remove_lcount_wl_heur_def isasat_assn_def
  supply [split] =  isasat_int.splits
  apply stuff_pre
  apply assumption
  apply (rule n[to_hnr, simplified, unfolded hn_refine_def, rule_format])
  apply (solves auto)
  apply (stuff_post1)
  apply assumption
  apply (stuff_post2)
  done

lemma remove_opts_wl_heur_int:
  \<open>(remove_opts_wl_heur_int, RETURN o remove_opts_wl_heur) \<in> isasat_assn\<^sup>d \<rightarrow>\<^sub>a o_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_opts_wl_heur_int_def remove_opts_wl_heur_def isasat_assn_def
  supply [split] =  isasat_int.splits
  apply stuff_pre
  apply assumption
  apply (rule o[to_hnr, simplified, unfolded hn_refine_def, rule_format])
  apply (solves auto)
  apply (stuff_post1)
  apply assumption
  apply (stuff_post2)
  done

lemma remove_old_arena_wl_heur_int:
  \<open>(remove_old_arena_wl_heur_int, RETURN o remove_old_arena_wl_heur) \<in> isasat_assn\<^sup>d \<rightarrow>\<^sub>a p_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_old_arena_wl_heur_int_def remove_old_arena_wl_heur_def isasat_assn_def
  supply [split] =  isasat_int.splits
  apply stuff_pre
  apply assumption
  apply (rule p[to_hnr, simplified, unfolded hn_refine_def, rule_format])
  apply (solves auto)
  apply (stuff_post1)
  apply assumption
  apply (stuff_post2)
  done

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

definition extract_literals_to_update_wl_heur where
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
  a = \<open>uncurry0 bottom_trail_code\<close> and
  b_default = bottom_arena and
  b = \<open>uncurry0 bottom_arena_code\<close> and
  c_default = bottom_conflict and
  c = \<open>uncurry0 bottom_conflict_code\<close> and
  d_default = \<open>bottom_decision_level\<close> and
  d = \<open>uncurry0 (bottom_decision_level_code)\<close> and
  e_default = bottom_watchlist and
  e = \<open>uncurry0 bottom_watchlist_code\<close> and
  f_default = bottom_vmtf and
  f = \<open>uncurry0 bottom_vmtf_code\<close> and
  g_default = bottom_clvls and
  g = \<open>uncurry0 bottom_clvls_code\<close>and
  h_default = bottom_ccach and
  h = \<open>uncurry0 bottom_ccach_code\<close> and
  i_default = empty_lbd and
  i = \<open>uncurry0 empty_lbd_code\<close>and
  j_default = bottom_outl and
  j = \<open>uncurry0 bottom_outl_code\<close> and
  k_default = bottom_stats and
  k = \<open>uncurry0 bottom_stats_code\<close> and
  l_default = bottom_heur and
  l = \<open>uncurry0 bottom_heur_code\<close> and
  m_default = bottom_vdom and
  m = \<open>uncurry0 bottom_vdom_code\<close> and
  n_default = bottom_lcount and
  n = \<open>uncurry0 bottom_lcount_code\<close> and
  ko_default = bottom_opts and
  ko = \<open>uncurry0 bottom_opts_code\<close> and
  p_default = bottom_old_arena and
  p = \<open>uncurry0 bottom_old_arena_code\<close>
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
    \<open>remove_outl_wl_heur \<equiv> extract_outl_wl_heur\<close> and
    \<open>remove_stats_wl_heur \<equiv> extract_stats_wl_heur\<close> and
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
  subgoal unfolding isasat_bounded_assn_def isasat_state_ops.isasat_assn_def .
  subgoal unfolding extract_trail_wl_heur_def .
  subgoal unfolding extract_arena_wl_heur_def .
  subgoal unfolding extract_conflict_wl_heur_def .
  subgoal unfolding extract_literals_to_update_wl_heur_def .
  subgoal unfolding extract_watchlist_wl_heur_def .
  subgoal unfolding extract_vmtf_wl_heur_def .
  subgoal unfolding extract_clvls_wl_heur_def .
  subgoal unfolding extract_ccach_wl_heur_def .
  subgoal unfolding extract_outl_wl_heur_def .
  subgoal unfolding extract_stats_wl_heur_def .
  subgoal unfolding extract_vdom_wl_heur_def .
  subgoal unfolding extract_lcount_wl_heur_def .
  subgoal unfolding extract_opts_wl_heur_def .
  subgoal unfolding extract_old_arena_wl_heur_def .
  done

lemmas [sepref_fr_rules] = remove_literals_to_update_wl_heur_int
  thm remove_literals_to_update_wl_heur_int
declare remove_literals_to_update_wl_heur_int_def[llvm_inline]


definition test2 where
  \<open>test2 M = do {a \<leftarrow> RETURN (extract_literals_to_update_wl_heur M);  (i, M) \<leftarrow> RETURN a; ASSERT (i+1 < 100); RETURN (i+1, M)}\<close>
sepref_register extract_literals_to_update_wl_heur
sepref_def test_impl3
  is \<open>test2\<close>
  :: \<open>isasat_bounded_assn\<^sup>d \<rightarrow>\<^sub>a sint64_nat_assn \<times>\<^sub>a isasat_bounded_assn\<close>
  supply [[goals_limit=1]]
  unfolding test2_def
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

   term ll_bpto
  lemma [llvm_pre_simp]: \<open>uncurry0 f () = f\<close>
     by auto

  thm remove_literals_to_update_wl_heur_int_def
export_llvm test_impl3

  sepref_def test
    is \<open>RETURN o remove_literals_to_update_wl_heur\<close>
    :: \<open>isasat_assn\<^sup>d \<rightarrow>\<^sub>a d_assn \<times>\<^sub>a isasat_assn\<close>
    unfolding remove_literals_to_update_wl_heur_def
    apply sepref
term isasat_bounded_assn
lemma [sepref_fr_rules]:
  \<open>(remove_literals_to_update_wl_heur_int, RETURN o remove_literals_to_update_wl_heur_int) \<in> isasat_assn\<^sup>d \<rightarrow>\<^sub>a arena_fast_assn \<times>\<^sub>a isasat_id_assn\<close>
  term aa
  term a
  supply [split] =  isasat_int.splits
  unfolding remove_literals_to_update_wl_heur_int_def
  apply sepref_to_hoare
  apply (case_tac x)
  apply vcg
  done
      find_theorems op_al_empty
find_theorems name:empty name:al
definition remove_literals_to_update_wl_heur where \<open>remove_literals_to_update_wl_heur = remove_literals_to_update_wl_heur_int\<close>

sepref_register remove_literals_to_update_wl_heur_int remove_literals_to_update_wl_heur
sepref_def remove_literals_to_update_wl_heur_impl
  is \<open>RETURN o remove_literals_to_update_wl_heur\<close>
  :: \<open>id_assn\<^sup>d \<rightarrow>\<^sub>a word64_assn \<times>\<^sub>a id_assn\<close>
  unfolding remove_literals_to_update_wl_heur_def
  by sepref


declare remove_literals_to_update_wl_heur_int_def[llvm_inline]
export_llvm test_impl3
term ll_pto
find_theorems "_ :: isasat_int \<Rightarrow> assn"

type_synonym twl_st_wll_trail_fast =
  \<open>trail_pol_fast_assn \<times> arena_assn \<times> option_lookup_clause_assn \<times>
    64 word \<times> watched_wl_uint32 \<times> vmtf_remove_assn \<times>
    32 word \<times> cach_refinement_l_assn \<times> lbd_assn \<times> out_learned_assn \<times> stats \<times>
    heur_assn \<times>
   aivdom_assn \<times> (64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word) \<times>
  opts_assn \<times> arena_assn\<close>


definition isasat_bounded_assn :: \<open>twl_st_wl_heur \<Rightarrow> twl_st_wll_trail_fast \<Rightarrow> assn\<close> where
\<open>isasat_bounded_assn =
  trail_pol_fast_assn \<times>\<^sub>a arena_fast_assn \<times>\<^sub>a
  conflict_option_rel_assn \<times>\<^sub>a
  sint64_nat_assn \<times>\<^sub>a
  watchlist_fast_assn \<times>\<^sub>a
  vmtf_remove_assn \<times>\<^sub>a
  uint32_nat_assn \<times>\<^sub>a
  cach_refinement_l_assn \<times>\<^sub>a
  lbd_assn \<times>\<^sub>a
  out_learned_assn \<times>\<^sub>a
  stats_assn \<times>\<^sub>a
  heuristic_assn \<times>\<^sub>a
  aivdom_assn \<times>\<^sub>a
  lcount_assn \<times>\<^sub>a
  opts_assn \<times>\<^sub>a arena_fast_assn\<close>

end
