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
    d_default :: 'd and
    d :: \<open>unit \<Rightarrow> 'xd llM\<close>
begin

definition isasat_assn :: \<open>_ \<Rightarrow> _ \<Rightarrow> assn\<close> where
\<open>isasat_assn = isasat_int_assn
  a_assn b_assn c_assn d_assn
  e_assn f_assn g_assn h_assn
  i_assn j_assn k_assn l_assn
  m_assn n_assn o_assn p_assn\<close>

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
end



locale isasat_state =
  isasat_state_ops a_assn b_assn c_assn d_assn e_assn
  f_assn g_assn h_assn i_assn j_assn
  k_assn l_assn m_assn n_assn o_assn p_assn
  a_default a
  d_default d
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
    d_default :: 'd and
    d :: \<open>unit \<Rightarrow> 'xd llM\<close> +
  assumes
    a: \<open>(a, uncurry0 (RETURN a_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a a_assn\<close> and
    d: \<open>(d, uncurry0 (RETURN d_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a d_assn\<close>
begin

lemmas [sepref_fr_rules] = d

lemma ex_isasat_int_iff: "(\<exists>b :: (_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_)isasat_int. P b) \<longleftrightarrow>
  (\<exists>a b  c d e f g h i j k l m n ko p. P (IsaSAT_int a b  c d e f g h i j k l m n ko p))"
  apply auto
    apply (case_tac b)
  by force
lemma remove_literals_to_update_wl_heur_int:
  \<open>(remove_literals_to_update_wl_heur_int, RETURN o remove_literals_to_update_wl_heur) \<in> isasat_assn\<^sup>d \<rightarrow>\<^sub>a d_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_literals_to_update_wl_heur_int_def remove_literals_to_update_wl_heur_def isasat_assn_def
  supply [split] =  isasat_int.splits
  apply sepref_to_hoare
  apply (case_tac x)
  apply vcg
  unfolding wpa_return
  apply auto
  apply (subst (asm)(2) sep_algebra_class.sep_conj_empty'[symmetric])
  apply (rule apply_htriple_rule)
  apply assumption
  apply (rule d[to_hnr, simplified, unfolded hn_refine_def, rule_format])
  apply auto[]
  apply (rule POSTCONDI)
  apply (rule STATE_monoI)
  apply assumption
  apply (auto simp: Exists_eq_simp ex_isasat_int_iff)
  subgoal premises p for x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x1a x2a x3a x4a x5a x6a x7a x8a x9a x10a x11a x12a x13a x14a x15a x16a asf s s' r
    by (smt (z3) entails_def entails_eq_iff pure_true_conv sep_conj_aci(4) sep_conj_aci(5) sep_conj_left_commute)
  done
end
definition extract_literals_to_update_wl_heur where
  \<open>extract_literals_to_update_wl_heur = isasat_state_ops.remove_literals_to_update_wl_heur 0\<close>

definition bottom_trail :: trail_pol where
  \<open>bottom_trail = do {
     let M0 = [] in
     let cs = [] in
     let M = replicate 0 UNSET in
     let M' = replicate 0 0 in
     let M'' = replicate 0 1 in
    ((M0, M, M', M'', 0, cs))
}\<close>

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
  d = \<open>uncurry0 (Mreturn 0)\<close> and
  d_default = \<open>0\<close>
  rewrites
    \<open>isasat_assn \<equiv> isasat_bounded_assn\<close> and
    \<open>remove_literals_to_update_wl_heur \<equiv> extract_literals_to_update_wl_heur\<close>
  apply unfold_locales
  subgoal by (rule bottom_trail_code.refine)
  subgoal
    by (sepref_to_hoare, vcg)
     (auto simp: snat_rel_def snat.rel_def br_def Exists_eq_simp snat_invar_0 pure_true_conv entails_def ENTAILS_def)
  subgoal
    unfolding isasat_bounded_assn_def isasat_state_ops.isasat_assn_def
    .
  subgoal
    unfolding extract_literals_to_update_wl_heur_def
      .
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
