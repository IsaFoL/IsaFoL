theory Tuple17_LLVM
  imports Tuple17 IsaSAT_Literals_LLVM
begin

hide_const (open) NEMonad.ASSERT NEMonad.RETURN


instantiation tuple17 ::
  (llvm_rep,llvm_rep,llvm_rep,llvm_rep,
  llvm_rep,llvm_rep,llvm_rep,llvm_rep,
  llvm_rep,llvm_rep,llvm_rep,llvm_rep,
  llvm_rep,llvm_rep,llvm_rep,llvm_rep,llvm_rep) llvm_rep
begin
  definition to_val_tuple17 where
    \<open>to_val_tuple17 \<equiv> (\<lambda>S. case S of
     Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs \<Rightarrow> LL_STRUCT [to_val M, to_val N, to_val D, to_val i, to_val W, to_val ivmtf,
       to_val icount, to_val ccach, to_val lbd,
       to_val outl, to_val stats, to_val heur, to_val aivdom,  to_val clss, to_val opts, to_val arena, to_val occs])\<close>

  definition from_val_tuple17 :: \<open>llvm_val \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
    \<open>from_val_tuple17 \<equiv> (\<lambda>p. case llvm_val.the_fields p of
   [M, N, D, i, W, ivmtf, icount, ccach, lbd, outl, stats, heur, aivdom, clss, opts, arena, occs] \<Rightarrow>
     Tuple17 (from_val M) (from_val N) (from_val D) (from_val i) (from_val W) (from_val ivmtf) (from_val icount) (from_val ccach) (from_val lbd)
       (from_val outl) (from_val stats) (from_val heur) (from_val aivdom) (from_val clss) (from_val opts) (from_val arena) (from_val occs))\<close>

  definition [simp]: "struct_of_tuple17 (_ :: ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 itself) \<equiv>
     VS_STRUCT [struct_of TYPE('a), struct_of TYPE('b), struct_of TYPE('c),
      struct_of TYPE('d), struct_of TYPE('e), struct_of TYPE('f), struct_of TYPE('g), struct_of TYPE('h),
      struct_of TYPE('i), struct_of TYPE('j), struct_of TYPE('k), struct_of TYPE('l),
      struct_of TYPE('m), struct_of TYPE('n), struct_of TYPE('o), struct_of TYPE('p),
      struct_of TYPE('q)]"

  definition [simp]: "init_tuple17 :: ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<equiv> Tuple17 init init init init init init init init init init init init init init init init init"

  instance
    apply standard
    unfolding from_val_tuple17_def to_val_tuple17_def struct_of_tuple17_def init_tuple17_def comp_def tuple17.case_distrib
    subgoal
      by (auto simp: init_zero fun_eq_iff from_val_tuple17_def split: tuple17.splits)
    subgoal for v
      by (cases v) (auto split: list.splits tuple17.splits)
    subgoal for v
      by (cases v)
       (simp add: LLVM_Shallow.null_def to_val_ptr_def split: tuple17.splits)
    subgoal
      by (simp add: LLVM_Shallow.null_def to_val_ptr_def to_val_word_def init_zero split: tuple17.splits)
    done
end

subsubsection \<open>Setup for LLVM code export\<close>

text \<open>Declare structure to code generator.\<close>
lemma to_val_tuple17[ll_struct_of]: "struct_of TYPE(('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17) = VS_STRUCT [
  struct_of TYPE('a::llvm_rep),
  struct_of TYPE('b::llvm_rep),
  struct_of TYPE('c::llvm_rep),
  struct_of TYPE('d::llvm_rep),
  struct_of TYPE('e::llvm_rep),
  struct_of TYPE('f::llvm_rep),
  struct_of TYPE('g::llvm_rep),
  struct_of TYPE('h::llvm_rep),
  struct_of TYPE('i::llvm_rep),
  struct_of TYPE('j::llvm_rep),
  struct_of TYPE('k::llvm_rep),
  struct_of TYPE('l::llvm_rep),
  struct_of TYPE('m::llvm_rep),
  struct_of TYPE('n::llvm_rep),
  struct_of TYPE('o::llvm_rep),
  struct_of TYPE('p::llvm_rep),
  struct_of TYPE('q::llvm_rep)]"
  by (auto)

text \<open>This is the old version of the declaration:\<close>
lemma "to_val x = LL_STRUCT [
  to_val (Tuple17_get_a x),
  to_val (Tuple17_get_b x),
  to_val (Tuple17_get_c x),
  to_val (Tuple17_get_d x),
  to_val (Tuple17_get_e x),
  to_val (Tuple17_get_f x),
  to_val (Tuple17_get_g x),
  to_val (Tuple17_get_h x),
  to_val (Tuple17_get_i x),
  to_val (Tuple17_get_j x),
  to_val (Tuple17_get_k x),
  to_val (Tuple17_get_l x),
  to_val (Tuple17_get_m x),
  to_val (Tuple17_get_n x),
  to_val (Tuple17_get_o x),
  to_val (Tuple17_get_p x),
  to_val (Tuple17_get_q x)]"
  apply (cases x)
  apply (auto simp: to_val_tuple17_def)
  done

lemma node_insert_value:
  "ll_insert_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) M' 0 = Mreturn (Tuple17 M' N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs)"
  "ll_insert_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) N' (Suc 0) = Mreturn (Tuple17 M N' D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs)"
  "ll_insert_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) D' 2 = Mreturn (Tuple17 M N D' i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs)"
  "ll_insert_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) i' 3 = Mreturn (Tuple17 M N D i' W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs)"
  "ll_insert_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) W' 4 = Mreturn (Tuple17 M N D i W' ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs)"
  "ll_insert_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) ivmtf' 5 = Mreturn (Tuple17 M N D i W ivmtf' icount ccach lbd outl stats heur aivdom clss opts arena occs)"
  "ll_insert_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) icount' 6 = Mreturn (Tuple17 M N D i W ivmtf icount' ccach lbd outl stats heur aivdom clss opts arena occs)"
  "ll_insert_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) ccach' 7 = Mreturn (Tuple17 M N D i W ivmtf icount ccach' lbd outl stats heur aivdom clss opts arena occs)"
  "ll_insert_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) lbd' 8 = Mreturn (Tuple17 M N D i W ivmtf icount ccach lbd' outl stats heur aivdom clss opts arena occs)"
  "ll_insert_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) outl' 9 = Mreturn (Tuple17 M N D i W ivmtf icount ccach lbd outl' stats heur aivdom clss opts arena occs)"
  "ll_insert_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) stats' 10 = Mreturn (Tuple17 M N D i W ivmtf icount ccach lbd outl stats' heur aivdom clss opts arena occs)"
  "ll_insert_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) heur' 11 = Mreturn (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur' aivdom clss opts arena occs)"
  "ll_insert_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) aivdom' 12 = Mreturn (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom' clss opts arena occs)"
  "ll_insert_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) clss' 13 = Mreturn (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss' opts arena occs)"
  "ll_insert_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) opts' 14 = Mreturn (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts' arena occs)"
  "ll_insert_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) arena' 15 = Mreturn (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena' occs)"
  "ll_insert_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) occs' 16 = Mreturn (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs')"
  by (simp_all add: ll_insert_value_def llvm_insert_value_def Let_def checked_from_val_def
                to_val_tuple17_def from_val_tuple17_def)

lemma node_extract_value:
  "ll_extract_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) 0 = Mreturn M"
  "ll_extract_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) (Suc 0) = Mreturn N"
  "ll_extract_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) 2 = Mreturn D"
  "ll_extract_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) 3 = Mreturn i"
  "ll_extract_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) 4 = Mreturn W"
  "ll_extract_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) 5 = Mreturn ivmtf"
  "ll_extract_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) 6 = Mreturn icount"
  "ll_extract_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) 7 = Mreturn ccach"
  "ll_extract_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) 8 = Mreturn lbd"
  "ll_extract_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) 9 = Mreturn outl"
  "ll_extract_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) 10 = Mreturn stats"
  "ll_extract_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) 11 = Mreturn heur"
  "ll_extract_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) 12 = Mreturn aivdom"
  "ll_extract_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) 13 = Mreturn clss"
  "ll_extract_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) 14 = Mreturn opts"
  "ll_extract_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) 15 = Mreturn arena"
  "ll_extract_value (Tuple17 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts arena occs) 16 = Mreturn occs"
  apply (simp_all add: ll_extract_value_def llvm_extract_value_def Let_def checked_from_val_def
                to_val_tuple17_def from_val_tuple17_def)
  done

text \<open>Lemmas to translate node construction and destruction\<close>
lemma inline_return_node[llvm_pre_simp]: "Mreturn (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs) = doM {
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
    r \<leftarrow> ll_insert_value r occs 16;
    Mreturn r
  }"
  apply (auto simp: node_insert_value)
  done

lemma inline_node_case[llvm_pre_simp]: "(case r of (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs) \<Rightarrow> f M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs) = doM {
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
    occs \<leftarrow> ll_extract_value r 16;
  f M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs
}"
  apply (cases r)
  apply (auto simp: node_extract_value)
  done

lemma inline_return_node_case[llvm_pre_simp]: "doM {Mreturn (case r of (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs) \<Rightarrow> f M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs)} = doM {
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
    occs \<leftarrow> ll_extract_value r 16;
  Mreturn (f M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs)
}"
  apply (cases r)
  apply (auto simp: node_extract_value)
  done
lemma inline_direct_return_node_case[llvm_pre_simp]: "doM {(case r of (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs) \<Rightarrow> f M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs)} = doM {
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
    occs \<leftarrow> ll_extract_value r 16;
   (f M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs)
}"
  apply (cases r)
  apply (auto simp: node_extract_value)
  done

lemmas [llvm_inline] =
  tuple17.Tuple17_get_a_def
  tuple17.Tuple17_get_b_def
  tuple17.Tuple17_get_c_def
  tuple17.Tuple17_get_d_def
  tuple17.Tuple17_get_e_def
  tuple17.Tuple17_get_f_def
  tuple17.Tuple17_get_g_def
  tuple17.Tuple17_get_h_def
  tuple17.Tuple17_get_i_def
  tuple17.Tuple17_get_j_def
  tuple17.Tuple17_get_l_def
  tuple17.Tuple17_get_k_def
  tuple17.Tuple17_get_m_def
  tuple17.Tuple17_get_n_def
  tuple17.Tuple17_get_o_def
  tuple17.Tuple17_get_p_def
  tuple17.Tuple17_get_q_def

fun tuple17_assn :: \<open>
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
  ('q \<Rightarrow> _ \<Rightarrow> llvm_amemory \<Rightarrow> bool) \<Rightarrow>
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>tuple17_assn a_assn b_assn' c_assn d_assn e_assn f_assn g_assn h_assn i_assn j_assn k_assn l_assn m_assn n_assn o_assn p_assn q_assn S T =
   (case (S, T) of
  (Tuple17 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts arena occs,
   Tuple17 M' N' D' i' W' ivmtf' icount' ccach' lbd' outl' heur' stats' aivdom' clss' opts' arena' occs')
     \<Rightarrow>
 (a_assn M (M') \<and>* b_assn' N (N') \<and>* c_assn D (D')  \<and>* d_assn i (i') \<and>*
 e_assn W (W') \<and>* f_assn ivmtf (ivmtf') \<and>* g_assn icount (icount')  \<and>* h_assn ccach (ccach') \<and>*
 i_assn lbd (lbd') \<and>* j_assn outl (outl') \<and>* k_assn heur (heur')  \<and>* l_assn stats (stats') \<and>*
 m_assn aivdom (aivdom') \<and>* n_assn clss (clss') \<and>* o_assn opts (opts')  \<and>* p_assn arena (arena')  \<and>* q_assn occs occs'))
  \<close>


locale isasat_state_ops =
  fixes
    a_assn :: \<open>'a \<Rightarrow> 'xa :: llvm_rep \<Rightarrow> assn\<close> and
    b_assn :: \<open>'b \<Rightarrow> 'xb:: llvm_rep \<Rightarrow> assn\<close> and
    c_assn :: \<open>'c \<Rightarrow> 'xc:: llvm_rep \<Rightarrow> assn\<close> and
    d_assn :: \<open>'d \<Rightarrow> 'xd:: llvm_rep \<Rightarrow> assn\<close> and
    e_assn :: \<open>'e \<Rightarrow> 'xe:: llvm_rep \<Rightarrow> assn\<close> and
    f_assn :: \<open>'f \<Rightarrow> 'xf:: llvm_rep \<Rightarrow> assn\<close> and
    g_assn :: \<open>'g \<Rightarrow> 'xg:: llvm_rep \<Rightarrow> assn\<close> and
    h_assn :: \<open>'h \<Rightarrow> 'xh:: llvm_rep \<Rightarrow> assn\<close> and
    i_assn :: \<open>'i \<Rightarrow> 'xi:: llvm_rep \<Rightarrow> assn\<close> and
    j_assn :: \<open>'j \<Rightarrow> 'xj:: llvm_rep \<Rightarrow> assn\<close> and
    k_assn :: \<open>'k \<Rightarrow> 'xk:: llvm_rep \<Rightarrow> assn\<close> and
    l_assn :: \<open>'l \<Rightarrow> 'xl:: llvm_rep \<Rightarrow> assn\<close> and
    m_assn :: \<open>'m \<Rightarrow> 'xm:: llvm_rep \<Rightarrow> assn\<close> and
    n_assn :: \<open>'n \<Rightarrow> 'xn:: llvm_rep \<Rightarrow> assn\<close> and
    o_assn :: \<open>'o \<Rightarrow> 'xo:: llvm_rep \<Rightarrow> assn\<close> and
    p_assn :: \<open>'p \<Rightarrow> 'xp:: llvm_rep \<Rightarrow> assn\<close> and
    q_assn :: \<open>'q \<Rightarrow> 'xq:: llvm_rep \<Rightarrow> assn\<close> and
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
    p :: \<open>'xp llM\<close>and
    q_default :: 'q and
    q :: \<open>'xq llM\<close>
begin

definition isasat_assn :: \<open>_ \<Rightarrow> _ \<Rightarrow> assn\<close> where
\<open>isasat_assn = tuple17_assn
  a_assn b_assn c_assn d_assn
  e_assn f_assn g_assn h_assn
  i_assn j_assn k_assn l_assn
  m_assn n_assn o_assn p_assn
  q_assn\<close>

definition remove_a :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _ \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>remove_a tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
      (x1, Tuple17 a_default x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17))\<close>

definition remove_b :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> 'b \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>remove_b tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
      (x2, Tuple17 x1 b_default x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17))\<close>

definition remove_c:: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _ \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>remove_c tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
      (x3, Tuple17 x1 x2 c_default x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17))\<close>

definition remove_d :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _ \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>remove_d tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
      (x4, Tuple17 x1 x2 x3 d_default x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17))\<close>

definition remove_e :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> 'e \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>remove_e tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
      (x5, Tuple17 x1 x2 x3 x4 e_default x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17))\<close>

definition remove_f :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> 'f \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>remove_f tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
      (x6, Tuple17 x1 x2 x3 x4 x5 f_default x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17))\<close>

definition remove_g :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> 'g \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>remove_g tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
      (x7, Tuple17 x1 x2 x3 x4 x5 x6 g_default x8 x9 x10 x11 x12 x13 x14 x15 x16 x17))\<close>

definition remove_h :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> 'h \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>remove_h tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
      (x8, Tuple17 x1 x2 x3 x4 x5 x6 x7 h_default x9 x10 x11 x12 x13 x14 x15 x16 x17))\<close>

definition remove_i :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> 'i \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>remove_i tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
      (x9, Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 i_default x10 x11 x12 x13 x14 x15 x16 x17))\<close>

definition remove_j :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> 'j \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>remove_j tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
      (x10, Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 j_default x11 x12 x13 x14 x15 x16 x17))\<close>

definition remove_k :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> 'k \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>remove_k tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
      (x11, Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 k_default x12 x13 x14 x15 x16 x17))\<close>

definition remove_l :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> 'l \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>remove_l tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
      (x12, Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 l_default x13 x14 x15 x16 x17))\<close>

definition remove_m :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> 'm \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>remove_m tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
      (x13, Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 m_default x14 x15 x16 x17))\<close>

definition remove_n :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> 'n \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>remove_n tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
      (x14, Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 n_default x15 x16 x17))\<close>

definition remove_o :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> 'o \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>remove_o tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
      (x15, Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ko_default x16 x17))\<close>

definition remove_p :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> 'p \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>remove_p tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
      (x16, Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 p_default x17))\<close>

definition remove_q :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> 'q \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>remove_q tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
      (x17, Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 q_default))\<close>

definition update_a :: \<open>'a \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>update_a x1 tuple17 = (case tuple17 of Tuple17 M x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
    let _ = M in
    Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17)\<close>

definition update_b :: \<open>'b \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>update_b x2 tuple17 = (case tuple17 of Tuple17 x1 M x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
    let _ = M in
    Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17)\<close>

definition update_c:: \<open>'c \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>update_c x3 tuple17 = (case tuple17 of Tuple17 x1 x2 M x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
    let _ = M in
    Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17)\<close>

definition update_d :: \<open>'d \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>update_d x4 tuple17 = (case tuple17 of Tuple17 x1 x2 x3 M x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
    let _ = M in
    Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17)\<close>

definition update_e :: \<open>'e \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>update_e x5 tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 M x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
    let _ = M in
    Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17)\<close>

definition update_f :: \<open>'f \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>update_f x6 tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 M x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
    let _ = M in
    Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17)\<close>

definition update_g :: \<open>'g \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>update_g x7 tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 M x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
    let _ = M in
    Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17)\<close>

definition update_h :: \<open>'h \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>update_h x8 tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 M x9 x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
    let _ = M in
    Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17)\<close>

definition update_i :: \<open>'i \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>update_i x9 tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 M x10 x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
    let _ = M in
    Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17)\<close>

definition update_j :: \<open>'j \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>update_j x10 tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 M x11 x12 x13 x14 x15 x16 x17 \<Rightarrow>
    let _ = M in
    Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17)\<close>

definition update_k :: \<open>'k \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>update_k x11 tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 M x12 x13 x14 x15 x16 x17 \<Rightarrow>
    let _ = M in
    Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17)\<close>

definition update_l :: \<open>'l \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>update_l x12 tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 M x13 x14 x15 x16 x17 \<Rightarrow>
    let _ = M in
    Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17)\<close>

definition update_m :: \<open>'m \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>update_m x13 tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 M x14 x15 x16 x17 \<Rightarrow>
    let _ = M in
    Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17)\<close>

definition update_n :: \<open>'n \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>update_n x14 tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 M x15 x16 x17 \<Rightarrow>
    let _ = M in
    Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17)\<close>

definition update_o :: \<open>'o \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>update_o x15 tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 M x16 x17 \<Rightarrow>
    let _ = M in
    Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17)\<close>


definition update_p :: \<open>'p \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>update_p x16 tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 M x17 \<Rightarrow>
    let _ = M in
    Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17)\<close>


definition update_q :: \<open>'q \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17\<close> where
  \<open>update_q x17 tuple17 = (case tuple17 of Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 M \<Rightarrow>
    let _ = M in
    Tuple17 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17)\<close>


end

lemma tuple17_assn_conv[simp]:
  "tuple17_assn P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 (Tuple17 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17)
  (Tuple17 a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15' a16' a17') =
  (P1 a1 a1' \<and>*
  P2 a2 a2' \<and>*
  P3 a3 a3' \<and>*
  P4 a4 a4' \<and>*
  P5 a5 a5' \<and>*
  P6 a6 a6' \<and>*
  P7 a7 a7' \<and>*
  P8 a8 a8' \<and>* P9 a9 a9' \<and>* P10 a10 a10' \<and>* P11 a11 a11' \<and>* P12 a12 a12' \<and>* P13 a13 a13' \<and>* P14 a14 a14' \<and>* P15 a15 a15' \<and>* P16 a16 a16'
  \<and>* P17 a17 a17')"
  unfolding tuple17_assn.simps by auto
lemma tuple17_assn_ctxt:
  \<open>tuple17_assn P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 (Tuple17 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17)
  (Tuple17 a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15' a16' a17') = z \<Longrightarrow>
  hn_ctxt (tuple17_assn P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17) (Tuple17 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17)
  (Tuple17 a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15' a16' a17')= z\<close>
  by (simp add: hn_ctxt_def)

lemma hn_case_tuple17'[sepref_comb_rules]:
  assumes FR: \<open>\<Gamma> \<turnstile> hn_ctxt (tuple17_assn P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17) p' p ** \<Gamma>1\<close>
  assumes Pair: "\<And>a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15' a16' a17'.
        \<lbrakk>p'=Tuple17 a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15' a16' a17'\<rbrakk>
    \<Longrightarrow> hn_refine (hn_ctxt P1 a1' a1 \<and>* hn_ctxt P2 a2' a2 \<and>* hn_ctxt P3 a3' a3 \<and>* hn_ctxt P4 a4' a4 \<and>*
       hn_ctxt P5 a5' a5 \<and>* hn_ctxt P6 a6' a6 \<and>* hn_ctxt P7 a7' a7 \<and>* hn_ctxt P8 a8' a8 \<and>*
       hn_ctxt P9 a9' a9 \<and>* hn_ctxt P10 a10' a10 \<and>* hn_ctxt P11 a11' a11 \<and>* hn_ctxt P12 a12' a12 \<and>*
       hn_ctxt P13 a13' a13 \<and>* hn_ctxt P14 a14' a14 \<and>* hn_ctxt P15 a15' a15 \<and>* hn_ctxt P16 a16' a16 \<and>* hn_ctxt P17 a17' a17 \<and>* \<Gamma>1)
          (f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17)
          (\<Gamma>2 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15' a16' a17') R
          (CP a1 a2  a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17)
         (f' a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15' a16' a17')"
  assumes FR2: \<open>\<And>a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15' a16' a17'.
       \<Gamma>2 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15' a16' a17' \<turnstile>
       hn_ctxt P1' a1' a1 ** hn_ctxt P2' a2' a2 ** hn_ctxt P3' a3' a3 ** hn_ctxt P4' a4' a4 **
       hn_ctxt P5' a5' a5 ** hn_ctxt P6' a6' a6 ** hn_ctxt P7' a7' a7 ** hn_ctxt P8' a8' a8 **
       hn_ctxt P9' a9' a9 ** hn_ctxt P10' a10' a10 ** hn_ctxt P11' a11' a11 ** hn_ctxt P12' a12' a12 **
       hn_ctxt P13' a13' a13 ** hn_ctxt P14' a14' a14 ** hn_ctxt P15' a15' a15 ** hn_ctxt P16' a16' a16 **
       hn_ctxt P17' a17' a17 ** \<Gamma>1'\<close>
  shows \<open>hn_refine \<Gamma> (case_tuple17 f p) (hn_ctxt (tuple17_assn P1' P2' P3' P4' P5' P6' P7' P8' P9' P10' P11' P12' P13' P14' P15' P16' P17') p' p ** \<Gamma>1')
    R (case_tuple17 CP p) (case_tuple17$(\<lambda>\<^sub>2a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17. f' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17)$p')\<close> (is \<open>?G \<Gamma>\<close>)
  unfolding autoref_tag_defs PROTECT2_def
  apply1 (rule hn_refine_cons_pre[OF FR])
    apply1 (cases p; cases p'; simp add: tuple17_assn_conv[THEN tuple17_assn_ctxt])
  unfolding CP_SPLIT_def prod.simps
  apply (rule hn_refine_cons[OF _ Pair _ entails_refl])
  applyS (simp add: hn_ctxt_def)
  applyS simp using FR2
  by (simp add: hn_ctxt_def)


lemma case_tuple17_arity[sepref_monadify_arity]:
  \<open>case_tuple17 \<equiv> \<lambda>\<^sub>2fp p. SP case_tuple17$(\<lambda>\<^sub>2a b. fp$a$b)$p\<close>
  by (simp_all only: SP_def APP_def PROTECT2_def RCALL_def)

lemma case_tuple17_comb[sepref_monadify_comb]:
  \<open>\<And>fp p. case_tuple17$fp$p \<equiv> Refine_Basic.bind$(EVAL$p)$(\<lambda>\<^sub>2p. (SP case_tuple17$fp$p))\<close>
  by (simp_all)

lemma case_tuple17_plain_comb[sepref_monadify_comb]:
  "EVAL$(case_tuple17$(\<lambda>\<^sub>2a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17. fp a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17)$p) \<equiv>
    Refine_Basic.bind$(EVAL$p)$(\<lambda>\<^sub>2p. case_tuple17$(\<lambda>\<^sub>2a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17. EVAL$(fp a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17))$p)"
  apply (rule eq_reflection, simp split: list.split prod.split option.split tuple17.split)+
  done

lemma ho_tuple17_move[sepref_preproc]: \<open>case_tuple17 (\<lambda>a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 x. f x a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17) =
  (\<lambda>p x. case_tuple17 (f x) p)\<close>
  by (auto split: tuple17.splits)

locale isasat_state =
  isasat_state_ops a_assn b_assn c_assn d_assn e_assn
  f_assn g_assn h_assn i_assn j_assn
  k_assn l_assn m_assn n_assn o_assn p_assn q_assn
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
  q_default q
  for
    a_assn :: \<open>'a \<Rightarrow> 'xa:: llvm_rep \<Rightarrow> assn\<close> and
    b_assn :: \<open>'b \<Rightarrow> 'xb:: llvm_rep \<Rightarrow> assn\<close> and
    c_assn :: \<open>'c \<Rightarrow> 'xc:: llvm_rep \<Rightarrow> assn\<close> and
    d_assn :: \<open>'d \<Rightarrow> 'xd:: llvm_rep \<Rightarrow> assn\<close> and
    e_assn :: \<open>'e \<Rightarrow> 'xe:: llvm_rep \<Rightarrow> assn\<close> and
    f_assn :: \<open>'f \<Rightarrow> 'xf:: llvm_rep \<Rightarrow> assn\<close> and
    g_assn :: \<open>'g \<Rightarrow> 'xg:: llvm_rep \<Rightarrow> assn\<close> and
    h_assn :: \<open>'h \<Rightarrow> 'xh:: llvm_rep \<Rightarrow> assn\<close> and
    i_assn :: \<open>'i \<Rightarrow> 'xi:: llvm_rep \<Rightarrow> assn\<close> and
    j_assn :: \<open>'j \<Rightarrow> 'xj:: llvm_rep \<Rightarrow> assn\<close> and
    k_assn :: \<open>'k \<Rightarrow> 'xk:: llvm_rep \<Rightarrow> assn\<close> and
    l_assn :: \<open>'l \<Rightarrow> 'xl:: llvm_rep \<Rightarrow> assn\<close> and
    m_assn :: \<open>'m \<Rightarrow> 'xm:: llvm_rep \<Rightarrow> assn\<close> and
    n_assn :: \<open>'n \<Rightarrow> 'xn:: llvm_rep \<Rightarrow> assn\<close> and
    o_assn :: \<open>'o \<Rightarrow> 'xo:: llvm_rep \<Rightarrow> assn\<close> and
    p_assn :: \<open>'p \<Rightarrow> 'xp:: llvm_rep \<Rightarrow> assn\<close> and
    q_assn :: \<open>'q \<Rightarrow> 'xq:: llvm_rep \<Rightarrow> assn\<close> and
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
    q_default :: 'q and
    q :: \<open>'xq llM\<close> and
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
    p_free :: \<open>'xp \<Rightarrow> unit llM\<close> and
    q_free :: \<open>'xq \<Rightarrow> unit llM\<close> +
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
    q: \<open>(uncurry0 q, uncurry0 (RETURN q_default)) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a q_assn\<close> and
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
    p_free: \<open>MK_FREE p_assn p_free\<close>and
    q_free: \<open>MK_FREE q_assn q_free\<close>
  notes [[sepref_register_adhoc a_default b_default c_default d_default e_default f_default g_default h_default
  i_default j_default k_default l_default m_default n_default ko_default p_default q_default]]
begin

lemmas [sepref_comb_rules] = hn_case_tuple17'[of _ a_assn b_assn c_assn d_assn e_assn f_assn
  g_assn h_assn i_assn j_assn k_assn l_assn m_assn n_assn o_assn p_assn q_assn,
  unfolded isasat_assn_def[symmetric]]

lemma ex_tuple17_iff: "(\<exists>b :: (_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_)tuple17. P b) \<longleftrightarrow>
  (\<exists>a b  c d e f g h i j k l m n ko p q. P (Tuple17 a b  c d e f g h i j k l m n ko p q))"
  apply auto
    apply (case_tac b)
  by force

lemmas [sepref_frame_free_rules] = a_free b_free c_free d_free e_free f_free g_free h_free i_free
  j_free k_free l_free m_free n_free o_free p_free q_free
sepref_register
  \<open>Tuple17\<close>
lemma [sepref_fr_rules]: \<open>(uncurry16 (Mreturn o\<^sub>1\<^sub>7 Tuple17), uncurry16 (RETURN o\<^sub>1\<^sub>7 Tuple17))
  \<in> a_assn\<^sup>d *\<^sub>a b_assn\<^sup>d *\<^sub>a c_assn\<^sup>d *\<^sub>a d_assn\<^sup>d *\<^sub>a
  e_assn\<^sup>d *\<^sub>a f_assn\<^sup>d *\<^sub>a g_assn\<^sup>d *\<^sub>a h_assn\<^sup>d *\<^sub>a
  i_assn\<^sup>d *\<^sub>a j_assn\<^sup>d *\<^sub>a k_assn\<^sup>d *\<^sub>a l_assn\<^sup>d *\<^sub>a
  m_assn\<^sup>d *\<^sub>a n_assn\<^sup>d *\<^sub>a o_assn\<^sup>d *\<^sub>a p_assn\<^sup>d *\<^sub>a
  q_assn\<^sup>d
  \<rightarrow>\<^sub>a isasat_assn\<close>
  unfolding isasat_assn_def
  apply sepref_to_hoare
  apply vcg
  unfolding ex_tuple17_iff
  apply vcg'
  done

lemma [sepref_frame_match_rules]:
  \<open> hn_ctxt
     (tuple17_assn (invalid_assn a_assn) (invalid_assn b_assn) (invalid_assn c_assn) (invalid_assn d_assn) (invalid_assn e_assn)
    (invalid_assn f_assn) (invalid_assn g_assn) (invalid_assn h_assn) (invalid_assn i_assn) (invalid_assn j_assn) (invalid_assn k_assn)
   (invalid_assn l_assn) (invalid_assn m_assn) (invalid_assn n_assn) (invalid_assn o_assn) (invalid_assn p_assn) (invalid_assn q_assn)) ax bx \<turnstile> hn_val UNIV ax bx\<close>
    unfolding hn_ctxt_def invalid_assn_def isasat_assn_def entails_def
    apply (auto split: prod.split tuple17.splits elim: is_pureE
      simp: sep_algebra_simps pure_part_pure_conj_eq)
    apply (auto simp: pure_part_def)
      apply (auto simp: pure_def pure_true_conv)
    done

lemma RETURN_case_tuple17_inverse: \<open>RETURN
      (let _ = M
         in ff) =
      (do {_ \<leftarrow> mop_free M;
         RETURN (ff)})\<close>
    by (auto intro!: ext simp: mop_free_def split: tuple17.splits)

sepref_def update_a_code
  is \<open>uncurry (RETURN oo update_a)\<close>
  :: \<open>a_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=5]]
  unfolding update_a_def tuple17.case_distrib comp_def RETURN_case_tuple17_inverse
  by sepref

sepref_def update_b_code
  is \<open>uncurry (RETURN oo update_b)\<close>
  :: \<open>b_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_b_def tuple17.case_distrib comp_def RETURN_case_tuple17_inverse
  by sepref

sepref_def update_c_code
  is \<open>uncurry (RETURN oo update_c)\<close>
  :: \<open>c_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_c_def tuple17.case_distrib comp_def RETURN_case_tuple17_inverse
  by sepref

sepref_def update_d_code
  is \<open>uncurry (RETURN oo update_d)\<close>
  :: \<open>d_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_d_def tuple17.case_distrib comp_def RETURN_case_tuple17_inverse
  by sepref

sepref_def update_e_code
  is \<open>uncurry (RETURN oo update_e)\<close>
  :: \<open>e_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_e_def tuple17.case_distrib comp_def RETURN_case_tuple17_inverse
  by sepref

sepref_def update_f_code
  is \<open>uncurry (RETURN oo update_f)\<close>
  :: \<open>f_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_f_def tuple17.case_distrib comp_def RETURN_case_tuple17_inverse
  by sepref

sepref_def update_g_code
  is \<open>uncurry (RETURN oo update_g)\<close>
  :: \<open>g_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_g_def tuple17.case_distrib comp_def RETURN_case_tuple17_inverse
  by sepref

sepref_def update_h_code
  is \<open>uncurry (RETURN oo update_h)\<close>
  :: \<open>h_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_h_def tuple17.case_distrib comp_def RETURN_case_tuple17_inverse
  by sepref

sepref_def update_i_code
  is \<open>uncurry (RETURN oo update_i)\<close>
  :: \<open>i_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_i_def tuple17.case_distrib comp_def RETURN_case_tuple17_inverse
  by sepref

sepref_def update_j_code
  is \<open>uncurry (RETURN oo update_j)\<close>
  :: \<open>j_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_j_def tuple17.case_distrib comp_def RETURN_case_tuple17_inverse
  by sepref

sepref_def update_k_code
  is \<open>uncurry (RETURN oo update_k)\<close>
  :: \<open>k_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_k_def tuple17.case_distrib comp_def RETURN_case_tuple17_inverse
  by sepref

sepref_def update_l_code
  is \<open>uncurry (RETURN oo update_l)\<close>
  :: \<open>l_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_l_def tuple17.case_distrib comp_def RETURN_case_tuple17_inverse
  by sepref

sepref_def update_m_code
  is \<open>uncurry (RETURN oo update_m)\<close>
  :: \<open>m_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_m_def tuple17.case_distrib comp_def RETURN_case_tuple17_inverse
  by sepref

sepref_def update_n_code
  is \<open>uncurry (RETURN oo update_n)\<close>
  :: \<open>n_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_n_def tuple17.case_distrib comp_def RETURN_case_tuple17_inverse
  by sepref

sepref_def update_o_code
  is \<open>uncurry (RETURN oo update_o)\<close>
  :: \<open>o_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_o_def tuple17.case_distrib comp_def RETURN_case_tuple17_inverse
  by sepref

sepref_def update_p_code
  is \<open>uncurry (RETURN oo update_p)\<close>
  :: \<open>p_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_p_def tuple17.case_distrib comp_def RETURN_case_tuple17_inverse
  by sepref

sepref_def update_q_code
  is \<open>uncurry (RETURN oo update_q)\<close>
  :: \<open>q_assn\<^sup>d *\<^sub>a isasat_assn\<^sup>d \<rightarrow>\<^sub>a isasat_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_q_def tuple17.case_distrib comp_def RETURN_case_tuple17_inverse
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
    unfold ex_tuple17_iff entails_def;
    auto simp: Exists_eq_simp ex_tuple17_iff  entails_def entails_eq_iff pure_true_conv sep_conj_left_commute;
    smt (z3) entails_def entails_eq_iff pure_true_conv sep_conj_aci(4) sep_conj_aci(5) sep_conj_left_commute

lemma RETURN_case_tuple17_invers: \<open>(RETURN \<circ>\<circ> case_tuple17)
   (\<lambda>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17.
  ff x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17) =
  case_tuple17
   (\<lambda>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17.
  RETURN (ff x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17))\<close>
  by (auto intro!: ext split: tuple17.splits)

lemmas [sepref_fr_rules] = a b c d e f g h i j k l m n  o p q

sepref_definition remove_a_code
  is \<open>RETURN o remove_a\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a a_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_a_def RETURN_case_tuple17_invers
  by sepref

sepref_definition remove_b_code
  is \<open>RETURN o remove_b\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a b_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_b_def RETURN_case_tuple17_invers
  by sepref

sepref_definition remove_c_code
  is \<open>RETURN o remove_c\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a c_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_c_def RETURN_case_tuple17_invers
  by sepref

sepref_definition remove_d_code
  is \<open>RETURN o remove_d\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a d_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_d_def RETURN_case_tuple17_invers
  by sepref

sepref_definition remove_e_code
  is \<open>RETURN o remove_e\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a e_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_e_def RETURN_case_tuple17_invers
  by sepref

sepref_definition remove_f_code
  is \<open>RETURN o remove_f\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a f_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_f_def RETURN_case_tuple17_invers
  by sepref

sepref_definition remove_g_code
  is \<open>RETURN o remove_g\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a g_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_g_def RETURN_case_tuple17_invers
  by sepref

sepref_definition remove_h_code
  is \<open>RETURN o remove_h\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a h_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_h_def RETURN_case_tuple17_invers
  by sepref

sepref_definition remove_i_code
  is \<open>RETURN o remove_i\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a i_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_i_def RETURN_case_tuple17_invers
  by sepref

sepref_definition remove_j_code
  is \<open>RETURN o remove_j\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a j_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_j_def RETURN_case_tuple17_invers
  by sepref

sepref_definition remove_k_code
  is \<open>RETURN o remove_k\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a k_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_k_def RETURN_case_tuple17_invers
  by sepref

sepref_definition remove_l_code
  is \<open>RETURN o remove_l\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a l_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_l_def RETURN_case_tuple17_invers
  by sepref

sepref_definition remove_m_code
  is \<open>RETURN o remove_m\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a m_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_m_def RETURN_case_tuple17_invers
  by sepref

sepref_definition remove_n_code
  is \<open>RETURN o remove_n\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a n_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_n_def RETURN_case_tuple17_invers
  by sepref

sepref_definition remove_o_code
  is \<open>RETURN o remove_o\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a o_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_o_def RETURN_case_tuple17_invers
  by sepref

sepref_definition remove_p_code
  is \<open>RETURN o remove_p\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a p_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_p_def RETURN_case_tuple17_invers
  by sepref

sepref_definition remove_q_code
  is \<open>RETURN o remove_q\<close>
  :: \<open> isasat_assn\<^sup>d \<rightarrow>\<^sub>a q_assn \<times>\<^sub>a isasat_assn\<close>
  unfolding remove_q_def RETURN_case_tuple17_invers
  by sepref


lemma remove_a_code_alt_def: \<open>remove_a_code xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 0;
              x \<leftarrow> a;
              x \<leftarrow> ll_insert_value xi x 0;
              return\<^sub>M (M, x)
  }\<close> and
  remove_b_code_alt_def: \<open>remove_b_code xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 1;
              x \<leftarrow> b;
              x \<leftarrow> ll_insert_value xi x 1;
              return\<^sub>M (M, x)
  }\<close>and
  remove_c_code_alt_def: \<open>remove_c_code xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 2;
              x \<leftarrow> c;
              x \<leftarrow> ll_insert_value xi x 2;
              return\<^sub>M (M, x)
  }\<close>and
  remove_d_code_alt_def: \<open>remove_d_code xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 3;
              x \<leftarrow> d;
              x \<leftarrow> ll_insert_value xi x 3;
              return\<^sub>M (M, x)
  }\<close>and
  remove_e_code_alt_def: \<open>remove_e_code xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 4;
              x \<leftarrow> e;
              x \<leftarrow> ll_insert_value xi x 4;
              return\<^sub>M (M, x)
  }\<close>and
  remove_f_code_alt_def: \<open>remove_f_code xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 5;
              x \<leftarrow> f;
              x \<leftarrow> ll_insert_value xi x 5;
              return\<^sub>M (M, x)
  }\<close>and
  remove_g_code_alt_def: \<open>remove_g_code xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 6;
              x \<leftarrow> g;
              x \<leftarrow> ll_insert_value xi x 6;
              return\<^sub>M (M, x)
  }\<close>and
  remove_h_code_alt_def: \<open>remove_h_code xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 7;
              x \<leftarrow> h;
              x \<leftarrow> ll_insert_value xi x 7;
              return\<^sub>M (M, x)
  }\<close>and
  remove_i_code_alt_def: \<open>remove_i_code xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 8;
              x \<leftarrow> i;
              x \<leftarrow> ll_insert_value xi x 8;
              return\<^sub>M (M, x)
  }\<close>and
  remove_j_code_alt_def: \<open>remove_j_code xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 9;
              x \<leftarrow> j;
              x \<leftarrow> ll_insert_value xi x 9;
              return\<^sub>M (M, x)
  }\<close>and
  remove_k_code_alt_def: \<open>remove_k_code xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 10;
              x \<leftarrow> k;
              x \<leftarrow> ll_insert_value xi x 10;
              return\<^sub>M (M, x)
  }\<close>and
  remove_l_code_alt_def: \<open>remove_l_code xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 11;
              x \<leftarrow> l;
              x \<leftarrow> ll_insert_value xi x 11;
              return\<^sub>M (M, x)
  }\<close>and
  remove_m_code_alt_def: \<open>remove_m_code xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 12;
              x \<leftarrow> m;
              x \<leftarrow> ll_insert_value xi x 12;
              return\<^sub>M (M, x)
  }\<close>and
  remove_n_code_alt_def: \<open>remove_n_code xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 13;
              x \<leftarrow> n;
              x \<leftarrow> ll_insert_value xi x 13;
              return\<^sub>M (M, x)
  }\<close>and
  remove_o_code_alt_def: \<open>remove_o_code xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 14;
              x \<leftarrow> ko;
              x \<leftarrow> ll_insert_value xi x 14;
              return\<^sub>M (M, x)
  }\<close>and
  remove_p_code_alt_def: \<open>remove_p_code xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 15;
              x \<leftarrow> p;
              x \<leftarrow> ll_insert_value xi x 15;
              return\<^sub>M (M, x)
  }\<close>and
  remove_q_code_alt_def: \<open>remove_q_code xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 16;
              x \<leftarrow> q;
              x \<leftarrow> ll_insert_value xi x 16;
              return\<^sub>M (M, x)
  }\<close>
  supply [simp] = llvm_extract_value_def
    ll_extract_value_def to_val_tuple17_def
    checked_from_val_def ll_insert_value_def
    llvm_insert_value_def
  unfolding remove_a_code_def remove_b_code_def inline_direct_return_node_case
    remove_c_code_def remove_d_code_def remove_e_code_def remove_f_code_def remove_g_code_def
    remove_h_code_def remove_i_code_def remove_j_code_def remove_k_code_def remove_l_code_def
    remove_m_code_def remove_n_code_def remove_o_code_def remove_p_code_def remove_q_code_def
  by (solves \<open>cases xi, rewrite in \<open>Mreturn (_, \<hole>)\<close> llvm_rep_class.from_to_id'[symmetric],
    simp flip: from_val_tuple17_def\<close>)+

lemma update_a_code_alt_def: \<open>\<And>x. update_a_code x xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 0; a_free M;
              x \<leftarrow> ll_insert_value xi x 0;
              return\<^sub>M (x)
  }\<close> and
  update_b_code_alt_def: \<open>\<And>x. update_b_code x xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 1; b_free M;
              x \<leftarrow> ll_insert_value xi x 1;
              return\<^sub>M (x)
  }\<close>and
  update_c_code_alt_def: \<open>\<And>x. update_c_code x xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 2; c_free M;
              x \<leftarrow> ll_insert_value xi x 2;
              return\<^sub>M (x)
  }\<close>and
  update_d_code_alt_def: \<open>\<And>x. update_d_code x xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 3; d_free M;
              x \<leftarrow> ll_insert_value xi x 3;
              return\<^sub>M (x)
  }\<close>and
  update_e_code_alt_def: \<open>\<And>x. update_e_code x xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 4; e_free M;
              x \<leftarrow> ll_insert_value xi x 4;
              return\<^sub>M (x)
  }\<close>and
  update_f_code_alt_def: \<open>\<And>x. update_f_code x xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 5; f_free M;
              x \<leftarrow> ll_insert_value xi x 5;
              return\<^sub>M (x)
  }\<close>and
  update_g_code_alt_def: \<open>\<And>x. update_g_code x xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 6; g_free M;
              x \<leftarrow> ll_insert_value xi x 6;
              return\<^sub>M (x)
  }\<close>and
  update_h_code_alt_def: \<open>\<And>x. update_h_code x xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 7; h_free M;
              x \<leftarrow> ll_insert_value xi x 7;
              return\<^sub>M (x)
  }\<close>and
  update_i_code_alt_def: \<open>\<And>x. update_i_code x xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 8; i_free M;
              x \<leftarrow> ll_insert_value xi x 8;
              return\<^sub>M (x)
  }\<close>and
  update_j_code_alt_def: \<open>\<And>x. update_j_code x xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 9; j_free M;
              x \<leftarrow> ll_insert_value xi x 9;
              return\<^sub>M (x)
  }\<close>and
  update_k_code_alt_def: \<open>\<And>x. update_k_code x xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 10; k_free M;
              x \<leftarrow> ll_insert_value xi x 10;
              return\<^sub>M (x)
  }\<close>and
  update_l_code_alt_def: \<open>\<And>x. update_l_code x xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 11; l_free M;
              x \<leftarrow> ll_insert_value xi x 11;
              return\<^sub>M (x)
  }\<close>and
  update_m_code_alt_def: \<open>\<And>x. update_m_code x xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 12; m_free M;
              x \<leftarrow> ll_insert_value xi x 12;
              return\<^sub>M (x)
  }\<close>and
  update_n_code_alt_def: \<open>\<And>x. update_n_code x xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 13; n_free M;
              x \<leftarrow> ll_insert_value xi x 13;
              return\<^sub>M (x)
  }\<close>and
  update_o_code_alt_def: \<open>\<And>x. update_o_code x xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 14; o_free M;
              x \<leftarrow> ll_insert_value xi x 14;
              return\<^sub>M (x)
  }\<close>and
  update_p_code_alt_def: \<open>\<And>x. update_p_code x xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 15; p_free M;
              x \<leftarrow> ll_insert_value xi x 15;
              return\<^sub>M (x)
  }\<close>and
  update_q_code_alt_def: \<open>\<And>x. update_q_code x xi = do\<^sub>M {
              M \<leftarrow> ll_extract_value xi 16; q_free M;
              x \<leftarrow> ll_insert_value xi x 16;
              return\<^sub>M (x)
  }\<close>
  supply [simp] = llvm_extract_value_def
    ll_extract_value_def to_val_tuple17_def
    checked_from_val_def ll_insert_value_def
    llvm_insert_value_def
  unfolding update_a_code_def update_b_code_def inline_direct_return_node_case
    update_c_code_def update_d_code_def update_e_code_def update_f_code_def update_g_code_def
    update_h_code_def update_i_code_def update_j_code_def update_k_code_def update_l_code_def
    update_m_code_def update_n_code_def update_o_code_def update_p_code_def update_q_code_def
    comp_def
  by (solves \<open>cases xi, rewrite in \<open>Mreturn (\<hole>)\<close> llvm_rep_class.from_to_id'[symmetric],
    simp flip: from_val_tuple17_def\<close>)+

end


context isasat_state
begin
lemma reconstruct_isasat[sepref_frame_match_rules]:
  \<open>hn_ctxt
     (tuple17_assn (a_assn) (b_assn) (c_assn) (d_assn) (e_assn)
    (f_assn) (g_assn) (h_assn) (i_assn) (j_assn) (k_assn)
   (l_assn) (m_assn) (n_assn) (o_assn) (p_assn) q_assn) ax bx \<turnstile> hn_ctxt isasat_assn ax bx\<close>
    unfolding isasat_assn_def
    apply (auto split: prod.split tuple17.splits elim: is_pureE
      simp: sep_algebra_simps pure_part_pure_conj_eq)
      done

context
  fixes x_assn :: \<open>'r \<Rightarrow> 'qst \<Rightarrow> assn\<close> and
    read_all_code :: \<open>'xa \<Rightarrow> 'xb \<Rightarrow> 'xc \<Rightarrow> 'xd \<Rightarrow> 'xe \<Rightarrow> 'xf \<Rightarrow> 'xg \<Rightarrow> 'xh \<Rightarrow> 'xi \<Rightarrow> 'xj \<Rightarrow> 'xk \<Rightarrow> 'xl \<Rightarrow> 'xm \<Rightarrow> 'xn \<Rightarrow> 'xo \<Rightarrow> 'xp \<Rightarrow> 'xq \<Rightarrow> 'qst llM\<close> and
    read_all :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'h \<Rightarrow> 'i \<Rightarrow> 'j \<Rightarrow> 'k \<Rightarrow> 'l \<Rightarrow> 'm \<Rightarrow> 'n \<Rightarrow> 'o \<Rightarrow> 'p \<Rightarrow> 'q \<Rightarrow> 'r nres\<close>
begin

definition read_all_st_code :: \<open>_\<close> where
  \<open>read_all_st_code xi = (case xi of
  Tuple17 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 \<Rightarrow>
    read_all_code a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17)\<close>

definition read_all_st :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o, 'p, 'q) tuple17 \<Rightarrow> _\<close> where
  \<open>read_all_st tuple17 = (case tuple17 of Tuple17 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 \<Rightarrow>
  read_all a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17)\<close>

context
  fixes P
  assumes trail_read[sepref_fr_rules]: \<open>(uncurry16 read_all_code, uncurry16 read_all) \<in>
      [uncurry16 P]\<^sub>a a_assn\<^sup>k *\<^sub>a b_assn\<^sup>k *\<^sub>a c_assn\<^sup>k *\<^sub>a d_assn\<^sup>k *\<^sub>a e_assn\<^sup>k *\<^sub>a f_assn\<^sup>k *\<^sub>a
          g_assn\<^sup>k *\<^sub>a h_assn\<^sup>k *\<^sub>a i_assn\<^sup>k *\<^sub>a j_assn\<^sup>k *\<^sub>a k_assn\<^sup>k *\<^sub>a l_assn\<^sup>k *\<^sub>a
          m_assn\<^sup>k *\<^sub>a n_assn\<^sup>k *\<^sub>a o_assn\<^sup>k *\<^sub>a p_assn\<^sup>k  *\<^sub>a q_assn\<^sup>k  \<rightarrow> x_assn\<close>
  notes [[sepref_register_adhoc read_all]]
begin
sepref_definition read_all_code_tmp
  is read_all_st
  :: \<open>[case_tuple17 P]\<^sub>a isasat_assn\<^sup>k \<rightarrow> x_assn\<close>
   unfolding read_all_st_def
   by sepref

lemmas read_all_code_refine =
  read_all_code_tmp.refine[unfolded read_all_code_tmp_def
    read_all_st_code_def[symmetric]]
end

end

lemmas [unfolded Let_def, tuple17_getters_setters] =
  update_a_def
  update_b_def
  update_c_def
  update_d_def
  update_e_def
  update_f_def
  update_g_def
  update_h_def
  update_i_def
  update_j_def
  update_k_def
  update_l_def
  update_m_def
  update_n_def
  update_o_def
  update_p_def
  update_q_def

  remove_a_def
  remove_b_def
  remove_c_def
  remove_d_def
  remove_e_def
  remove_f_def
  remove_g_def
  remove_h_def
  remove_i_def
  remove_j_def
  remove_k_def
  remove_l_def
  remove_m_def
  remove_n_def
  remove_o_def
  remove_p_def
  remove_q_def

end

lemmas [tuple17_getters_setters] =
  isasat_state_ops.remove_a_def
  isasat_state_ops.remove_b_def
  isasat_state_ops.remove_c_def
  isasat_state_ops.remove_d_def
  isasat_state_ops.remove_e_def
  isasat_state_ops.remove_f_def
  isasat_state_ops.remove_g_def
  isasat_state_ops.remove_h_def
  isasat_state_ops.remove_i_def
  isasat_state_ops.remove_j_def
  isasat_state_ops.remove_k_def
  isasat_state_ops.remove_l_def
  isasat_state_ops.remove_m_def
  isasat_state_ops.remove_n_def
  isasat_state_ops.remove_o_def
  isasat_state_ops.remove_p_def
  isasat_state_ops.remove_q_def

end
