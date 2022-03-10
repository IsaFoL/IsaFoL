theory Tuple15_LLVM
  imports Tuple15 IsaSAT_Literals_LLVM
begin

no_notation WB_More_Refinement.fref (\<open>[_]\<^sub>f _ \<rightarrow> _\<close> [0,60,60] 60)
no_notation WB_More_Refinement.freft (\<open>_ \<rightarrow>\<^sub>f _\<close> [60,60] 60)
hide_const (open) NEMonad.ASSERT NEMonad.RETURN

text \<open>
This is the setup for accessing and modifying the state as an abstract tuple of 15 elements.
 The construction is kept generic 
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

instantiation tuple15 ::
  (llvm_rep,llvm_rep,llvm_rep,llvm_rep,
  llvm_rep,llvm_rep,llvm_rep,llvm_rep,
  llvm_rep,llvm_rep,llvm_rep,llvm_rep,
  llvm_rep,llvm_rep,llvm_rep) llvm_rep
begin
  definition to_val_tuple15 where
    \<open>to_val_tuple15 \<equiv> (\<lambda>S. case S of
     Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts \<Rightarrow> LL_STRUCT [to_val M, to_val N, to_val D, to_val i, to_val W, to_val ivmtf,
       to_val icount, to_val ccach, to_val lbd,
       to_val outl, to_val stats, to_val heur, to_val aivdom,  to_val clss, to_val opts])\<close>

  definition from_val_tuple15 :: \<open>llvm_val \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15\<close> where
    \<open>from_val_tuple15 \<equiv> (\<lambda>p. case llvm_val.the_fields p of
   [M, N, D, i, W, ivmtf, icount, ccach, lbd, outl, stats, heur, aivdom, clss, opts] \<Rightarrow>
     Tuple15 (from_val M) (from_val N) (from_val D) (from_val i) (from_val W) (from_val ivmtf) (from_val icount) (from_val ccach) (from_val lbd)
       (from_val outl) (from_val stats) (from_val heur) (from_val aivdom) (from_val clss) (from_val opts))\<close>

  definition [simp]: "struct_of_tuple15 (_ :: ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15 itself) \<equiv>
     VS_STRUCT [struct_of TYPE('a), struct_of TYPE('b), struct_of TYPE('c),
      struct_of TYPE('d), struct_of TYPE('e), struct_of TYPE('f), struct_of TYPE('g), struct_of TYPE('h),
      struct_of TYPE('i), struct_of TYPE('j), struct_of TYPE('k), struct_of TYPE('l),
      struct_of TYPE('m), struct_of TYPE('n), struct_of TYPE('o)]"

  definition [simp]: "init_tuple15 :: ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j, 'k, 'l, 'm, 'n, 'o) tuple15 \<equiv> Tuple15 init init init init init init init init init init init init init init init"

  instance
    apply standard
    unfolding from_val_tuple15_def to_val_tuple15_def struct_of_tuple15_def init_tuple15_def comp_def tuple15.case_distrib
    subgoal
      by (auto simp: init_zero fun_eq_iff from_val_tuple15_def split: tuple15.splits)
    subgoal for v
      by (cases v) (auto split: list.splits tuple15.splits)
    subgoal for v
      by (cases v)
       (simp add: LLVM_Shallow.null_def to_val_ptr_def split: tuple15.splits)
    subgoal
      by (simp add: LLVM_Shallow.null_def to_val_ptr_def to_val_word_def init_zero split: tuple15.splits)
    done
end

subsubsection \<open>Setup for LLVM code export\<close>
text \<open>Declare structure to code generator.\<close>
lemma to_val_tuple15[ll_to_val]: "to_val x = LL_STRUCT [
  to_val (Tuple15_a x),
  to_val (Tuple15_b x),
  to_val (Tuple15_c x),
  to_val (Tuple15_d x),
  to_val (Tuple15_e x),
  to_val (Tuple15_f x),
  to_val (Tuple15_g x),
  to_val (Tuple15_h x),
  to_val (Tuple15_i x),
  to_val (Tuple15_j x),
  to_val (Tuple15_k x),
  to_val (Tuple15_l x),
  to_val (Tuple15_m x),
  to_val (Tuple15_n x),
  to_val (Tuple15_o x)]"
  apply (cases x)
  apply (auto simp: to_val_tuple15_def)
  done

lemma node_insert_value:
  "ll_insert_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) M' 0 = Mreturn (Tuple15 M' N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts)"
  "ll_insert_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) N' (Suc 0) = Mreturn (Tuple15 M N' D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts)"
  "ll_insert_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) D' 2 = Mreturn (Tuple15 M N D' i W ivmtf icount ccach lbd outl stats heur aivdom clss opts)"
  "ll_insert_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) i' 3 = Mreturn (Tuple15 M N D i' W ivmtf icount ccach lbd outl stats heur aivdom clss opts)"
  "ll_insert_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) W' 4 = Mreturn (Tuple15 M N D i W' ivmtf icount ccach lbd outl stats heur aivdom clss opts)"
  "ll_insert_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) ivmtf' 5 = Mreturn (Tuple15 M N D i W ivmtf' icount ccach lbd outl stats heur aivdom clss opts)"
  "ll_insert_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) icount' 6 = Mreturn (Tuple15 M N D i W ivmtf icount' ccach lbd outl stats heur aivdom clss opts)"
  "ll_insert_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) ccach' 7 = Mreturn (Tuple15 M N D i W ivmtf icount ccach' lbd outl stats heur aivdom clss opts)"
  "ll_insert_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) lbd' 8 = Mreturn (Tuple15 M N D i W ivmtf icount ccach lbd' outl stats heur aivdom clss opts)"
  "ll_insert_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) outl' 9 = Mreturn (Tuple15 M N D i W ivmtf icount ccach lbd outl' stats heur aivdom clss opts)"
  "ll_insert_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) stats' 10 = Mreturn (Tuple15 M N D i W ivmtf icount ccach lbd outl stats' heur aivdom clss opts)"
  "ll_insert_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) heur' 11 = Mreturn (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur' aivdom clss opts)"
  "ll_insert_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) aivdom' 12 = Mreturn (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom' clss opts)"
  "ll_insert_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) clss' 13 = Mreturn (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss' opts)"
  "ll_insert_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) opts' 14 = Mreturn (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts')"
  by (simp_all add: ll_insert_value_def llvm_insert_value_def Let_def checked_from_val_def
                to_val_tuple15_def from_val_tuple15_def)

lemma node_extract_value:
  "ll_extract_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) 0 = Mreturn M"
  "ll_extract_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) (Suc 0) = Mreturn N"
  "ll_extract_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) 2 = Mreturn D"
  "ll_extract_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) 3 = Mreturn i"
  "ll_extract_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) 4 = Mreturn W"
  "ll_extract_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) 5 = Mreturn ivmtf"
  "ll_extract_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) 6 = Mreturn icount"
  "ll_extract_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) 7 = Mreturn ccach"
  "ll_extract_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) 8 = Mreturn lbd"
  "ll_extract_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) 9 = Mreturn outl"
  "ll_extract_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) 10 = Mreturn stats"
  "ll_extract_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) 11 = Mreturn heur"
  "ll_extract_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) 12 = Mreturn aivdom"
  "ll_extract_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) 13 = Mreturn clss"
  "ll_extract_value (Tuple15 M N D i W ivmtf icount ccach lbd outl stats heur aivdom clss opts) 14 = Mreturn opts"
  apply (simp_all add: ll_extract_value_def llvm_extract_value_def Let_def checked_from_val_def
                to_val_tuple15_def from_val_tuple15_def)
  done

text \<open>Lemmas to translate node construction and destruction\<close>
lemma inline_return_node[llvm_pre_simp]: "Mreturn (Tuple15 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts) = doM {
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
    Mreturn r
  }"
  apply (auto simp: node_insert_value)
  done

lemma inline_node_case[llvm_pre_simp]: "(case r of (Tuple15 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts) \<Rightarrow> f M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts) = doM {
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
  f M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts
}"
  apply (cases r)
  apply (auto simp: node_extract_value)
  done

lemma inline_return_node_case[llvm_pre_simp]: "doM {Mreturn (case r of (Tuple15 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts) \<Rightarrow> f M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts)} = doM {
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
  Mreturn (f M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts)
}"
  apply (cases r)
  apply (auto simp: node_extract_value)
  done
lemma inline_direct_return_node_case[llvm_pre_simp]: "doM {(case r of (Tuple15 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts) \<Rightarrow> f M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts)} = doM {
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
   (f M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts)
}"
  apply (cases r)
  apply (auto simp: node_extract_value)
  done

lemmas [llvm_inline] =
  tuple15.Tuple15_a_def
  tuple15.Tuple15_b_def
  tuple15.Tuple15_c_def
  tuple15.Tuple15_d_def
  tuple15.Tuple15_e_def
  tuple15.Tuple15_f_def
  tuple15.Tuple15_g_def
  tuple15.Tuple15_h_def
  tuple15.Tuple15_i_def
  tuple15.Tuple15_j_def
  tuple15.Tuple15_k_def
  tuple15.Tuple15_l_def
  tuple15.Tuple15_m_def
  tuple15.Tuple15_n_def
  tuple15.Tuple15_o_def

fun tuple15_assn :: \<open>
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
  ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> _ \<Rightarrow> assn\<close> where
  \<open>tuple15_assn a_assn b_assn' c_assn d_assn e_assn f_assn g_assn h_assn i_assn j_assn k_assn l_assn m_assn n_assn o_assn S T =
   (case (S, T) of
  (Tuple15 M N D i W ivmtf icount ccach lbd outl heur stats aivdom clss opts,
   Tuple15 M' N' D' i' W' ivmtf' icount' ccach' lbd' outl' heur' stats' aivdom' clss' opts')
     \<Rightarrow>
 (a_assn M (M') \<and>* b_assn' N (N') \<and>* c_assn D (D')  \<and>* d_assn i (i') \<and>*
 e_assn W (W') \<and>* f_assn ivmtf (ivmtf') \<and>* g_assn icount (icount')  \<and>* h_assn ccach (ccach') \<and>*
 i_assn lbd (lbd') \<and>* j_assn outl (outl') \<and>* k_assn heur (heur')  \<and>* l_assn stats (stats') \<and>*
 m_assn aivdom (aivdom') \<and>* n_assn clss (clss') \<and>* o_assn opts (opts')))
  \<close>

locale tuple15_state_ops =
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
    ko :: \<open>'xo llM\<close>
begin

definition tuple15_int_assn :: \<open>_ \<Rightarrow> _ \<Rightarrow> assn\<close> where
\<open>tuple15_int_assn = tuple15_assn
  a_assn b_assn c_assn d_assn
  e_assn f_assn g_assn h_assn
  i_assn j_assn k_assn l_assn
  m_assn n_assn o_assn\<close>

definition remove_a :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> 'a \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>remove_a tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
      (x1, Tuple15 a_default x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15))\<close>

definition remove_b :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> 'b \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>remove_b tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
      (x2, Tuple15 x1 b_default x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15))\<close>

definition remove_c :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> _ \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>remove_c tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
      (x3, Tuple15 x1 x2 c_default x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15))\<close>

definition remove_d :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> _ \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>remove_d tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
      (x4, Tuple15 x1 x2 x3 d_default x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15))\<close>

definition remove_e :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> 'e \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>remove_e tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
      (x5, Tuple15 x1 x2 x3 x4 e_default x6 x7 x8 x9 x10 x11 x12 x13 x14 x15))\<close>

definition remove_f :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> 'f \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>remove_f tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
      (x6, Tuple15 x1 x2 x3 x4 x5 f_default x7 x8 x9 x10 x11 x12 x13 x14 x15))\<close>

definition remove_g :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> 'g \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>remove_g tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
      (x7, Tuple15 x1 x2 x3 x4 x5 x6 g_default x8 x9 x10 x11 x12 x13 x14 x15))\<close>

definition remove_h :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> 'h \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>remove_h tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
      (x8, Tuple15 x1 x2 x3 x4 x5 x6 x7 h_default x9 x10 x11 x12 x13 x14 x15))\<close>

definition remove_i :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> 'i \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>remove_i tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
      (x9, Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 i_default x10 x11 x12 x13 x14 x15))\<close>

definition remove_j :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> 'j \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>remove_j tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
      (x10, Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 j_default x11 x12 x13 x14 x15))\<close>

definition remove_k :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> 'k \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>remove_k tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
      (x11, Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 k_default x12 x13 x14 x15))\<close>

definition remove_l :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> 'l \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>remove_l tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
      (x12, Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 l_default x13 x14 x15))\<close>

definition remove_m :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> 'm \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>remove_m tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
      (x13, Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 m_default x14 x15))\<close>

definition remove_n :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> 'n \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>remove_n tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
      (x14, Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 n_default x15))\<close>

definition remove_o :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> 'o \<times> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>remove_o tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
      (x15, Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 ko_default))\<close>

definition update_a :: \<open>'a \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>update_a x1 tuple15 = (case tuple15 of Tuple15 M x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
    let _ = M in
    Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)\<close>

definition update_b :: \<open>'b \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>update_b x2 tuple15 = (case tuple15 of Tuple15 x1 M x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
    let _ = M in
    Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)\<close>

definition update_c :: \<open>'c \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>update_c x3 tuple15 = (case tuple15 of Tuple15 x1 x2 M x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
    let _ = M in
    Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)\<close>

definition update_d :: \<open>'d \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>update_d x4 tuple15 = (case tuple15 of Tuple15 x1 x2 x3 M x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
    let _ = M in
    Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)\<close>

definition update_e :: \<open>'e \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>update_e x5 tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 M x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
    let _ = M in
    Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)\<close>

definition update_f :: \<open>'f \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>update_f x6 tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 M x7 x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
    let _ = M in
    Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)\<close>

definition update_g :: \<open>'g \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>update_g x7 tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 M x8 x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
    let _ = M in
    Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)\<close>

definition update_h :: \<open>'h \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>update_h x8 tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 M x9 x10 x11 x12 x13 x14 x15 \<Rightarrow>
    let _ = M in
    Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)\<close>

definition update_i :: \<open>'i \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>update_i x9 tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 M x10 x11 x12 x13 x14 x15 \<Rightarrow>
    let _ = M in
    Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)\<close>

definition update_j :: \<open>'j \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>update_j x10 tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 M x11 x12 x13 x14 x15 \<Rightarrow>
    let _ = M in
    Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)\<close>

definition update_k :: \<open>'k \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>update_k x11 tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 M x12 x13 x14 x15 \<Rightarrow>
    let _ = M in
    Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)\<close>

definition update_l :: \<open>'l \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>update_l x12 tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 M x13 x14 x15 \<Rightarrow>
    let _ = M in
    Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)\<close>

definition update_m :: \<open>'m \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>update_m x13 tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 M x14 x15 \<Rightarrow>
    let _ = M in
    Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)\<close>

definition update_n :: \<open>'n \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>update_n x14 tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 M x15 \<Rightarrow>
    let _ = M in
    Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)\<close>

definition update_o :: \<open>'o \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> ('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15\<close> where
  \<open>update_o x15 tuple15 = (case tuple15 of Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 M \<Rightarrow>
    let _ = M in
    Tuple15 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15)\<close>


end
 
lemma tuple15_assn_conv[simp]: 
  "tuple15_assn P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 (Tuple15 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)
  (Tuple15 a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15') =
  (P1 a1 a1' \<and>*
  P2 a2 a2' \<and>*
  P3 a3 a3' \<and>*
  P4 a4 a4' \<and>*
  P5 a5 a5' \<and>*
  P6 a6 a6' \<and>*
  P7 a7 a7' \<and>*
  P8 a8 a8' \<and>* P9 a9 a9' \<and>* P10 a10 a10' \<and>* P11 a11 a11' \<and>* P12 a12 a12' \<and>* P13 a13 a13' \<and>* P14 a14 a14' \<and>* P15 a15 a15')"
  unfolding tuple15_assn.simps by auto
lemma tuple15_assn_ctxt:
  \<open>tuple15_assn P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 (Tuple15 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)
  (Tuple15 a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15') = z \<Longrightarrow>
  hn_ctxt (tuple15_assn P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15) (Tuple15 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)
  (Tuple15 a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15')= z\<close>
  by (simp add: hn_ctxt_def)

lemma hn_case_tuple15'[sepref_comb_rules]:
  assumes FR: \<open>\<Gamma> \<turnstile> hn_ctxt (tuple15_assn P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15) p' p ** \<Gamma>1\<close>
  assumes Pair: "\<And>a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15'.
        \<lbrakk>p'=Tuple15 a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15'\<rbrakk>
    \<Longrightarrow> hn_refine (hn_ctxt P1 a1' a1 \<and>* hn_ctxt P2 a2' a2 \<and>* hn_ctxt P3 a3' a3 \<and>* hn_ctxt P4 a4' a4 \<and>*
       hn_ctxt P5 a5' a5 \<and>* hn_ctxt P6 a6' a6 \<and>* hn_ctxt P7 a7' a7 \<and>* hn_ctxt P8 a8' a8 \<and>*
       hn_ctxt P9 a9' a9 \<and>* hn_ctxt P10 a10' a10 \<and>* hn_ctxt P11 a11' a11 \<and>* hn_ctxt P12 a12' a12 \<and>*
       hn_ctxt P13 a13' a13 \<and>* hn_ctxt P14 a14' a14 \<and>* hn_ctxt P15 a15' a15 \<and>* \<Gamma>1)
          (f a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)
          (\<Gamma>2 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15') R
          (CP a1 a2  a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)
         (f' a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15')"
  assumes FR2: \<open>\<And>a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15'.
       \<Gamma>2 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a1' a2' a3' a4' a5' a6' a7' a8' a9' a10' a11' a12' a13' a14' a15' \<turnstile>
       hn_ctxt P1' a1' a1 ** hn_ctxt P2' a2' a2 ** hn_ctxt P3' a3' a3 ** hn_ctxt P4' a4' a4 **
       hn_ctxt P5' a5' a5 ** hn_ctxt P6' a6' a6 ** hn_ctxt P7' a7' a7 ** hn_ctxt P8' a8' a8 **
       hn_ctxt P9' a9' a9 ** hn_ctxt P10' a10' a10 ** hn_ctxt P11' a11' a11 ** hn_ctxt P12' a12' a12 **
       hn_ctxt P13' a13' a13 ** hn_ctxt P14' a14' a14 ** hn_ctxt P15' a15' a15 ** \<Gamma>1'\<close>
  shows \<open>hn_refine \<Gamma> (case_tuple15 f p) (hn_ctxt (tuple15_assn P1' P2' P3' P4' P5' P6' P7' P8' P9' P10' P11' P12' P13' P14' P15') p' p ** \<Gamma>1')
    R (case_tuple15 CP p) (case_tuple15$(\<lambda>\<^sub>2a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15. f' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)$p')\<close> (is \<open>?G \<Gamma>\<close>)
  unfolding autoref_tag_defs PROTECT2_def
  apply1 (rule hn_refine_cons_pre[OF FR])
    apply1 (cases p; cases p'; simp add: tuple15_assn_conv[THEN tuple15_assn_ctxt])
  unfolding CP_SPLIT_def prod.simps
  apply (rule hn_refine_cons[OF _ Pair _ entails_refl])
  applyS (simp add: hn_ctxt_def)
  applyS simp using FR2
  by (simp add: hn_ctxt_def)


lemma case_tuple15_arity[sepref_monadify_arity]:
  \<open>case_tuple15 \<equiv> \<lambda>\<^sub>2fp p. SP case_tuple15$(\<lambda>\<^sub>2a b. fp$a$b)$p\<close>
  by (simp_all only: SP_def APP_def PROTECT2_def RCALL_def)

lemma case_tuple15_comb[sepref_monadify_comb]:
  \<open>\<And>fp p. case_tuple15$fp$p \<equiv> Refine_Basic.bind$(EVAL$p)$(\<lambda>\<^sub>2p. (SP case_tuple15$fp$p))\<close>
  by (simp_all)

lemma case_tuple15_plain_comb[sepref_monadify_comb]:
  "EVAL$(case_tuple15$(\<lambda>\<^sub>2a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15. fp a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)$p) \<equiv>
    Refine_Basic.bind$(EVAL$p)$(\<lambda>\<^sub>2p. case_tuple15$(\<lambda>\<^sub>2a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15. EVAL$(fp a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15))$p)"
  apply (rule eq_reflection, simp split: list.split prod.split option.split tuple15.split)+
  done

lemma ho_tuple15_move[sepref_preproc]: \<open>case_tuple15 (\<lambda>a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 x. f x a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15) =
  (\<lambda>p x. case_tuple15 (f x) p)\<close>
  by (auto split: tuple15.splits)

locale tuple15_state =
  tuple15_state_ops a_assn b_assn c_assn d_assn e_assn
  f_assn g_assn h_assn i_assn j_assn
  k_assn l_assn m_assn n_assn o_assn
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
    o_free :: \<open>'xo \<Rightarrow> unit llM\<close> +
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
    o_free: \<open>MK_FREE o_assn o_free\<close>
  notes [[sepref_register_adhoc a_default b_default c_default d_default e_default f_default g_default h_default
  i_default j_default k_default l_default m_default n_default ko_default p_default]]
begin

lemmas [sepref_comb_rules] = hn_case_tuple15'[of _ a_assn b_assn c_assn d_assn e_assn f_assn
  g_assn h_assn i_assn j_assn k_assn l_assn m_assn n_assn o_assn,
  unfolded tuple15_int_assn_def[symmetric]]

lemma ex_tuple15_iff: "(\<exists>b :: (_,_,_,_,_,_,_,_,_,_,_,_,_,_,_)tuple15. P b) \<longleftrightarrow>
  (\<exists>a b  c d e f g h i j k l m n ko. P (Tuple15 a b  c d e f g h i j k l m n ko))"
  apply auto
    apply (case_tac b)
  by force

lemmas [sepref_frame_free_rules] = a_free b_free c_free d_free e_free f_free g_free h_free i_free
  j_free k_free l_free m_free n_free o_free
sepref_register
  \<open>Tuple15\<close>
lemma [sepref_fr_rules]: \<open>(uncurry14 (Mreturn o\<^sub>1\<^sub>5 Tuple15), uncurry14 (RETURN o\<^sub>1\<^sub>5 Tuple15))
  \<in> a_assn\<^sup>d *\<^sub>a b_assn\<^sup>d *\<^sub>a c_assn\<^sup>d *\<^sub>a d_assn\<^sup>d *\<^sub>a
  e_assn\<^sup>d *\<^sub>a f_assn\<^sup>d *\<^sub>a g_assn\<^sup>d *\<^sub>a h_assn\<^sup>d *\<^sub>a
  i_assn\<^sup>d *\<^sub>a j_assn\<^sup>d *\<^sub>a k_assn\<^sup>d *\<^sub>a l_assn\<^sup>d *\<^sub>a
  m_assn\<^sup>d *\<^sub>a n_assn\<^sup>d *\<^sub>a o_assn\<^sup>d
  \<rightarrow>\<^sub>a tuple15_int_assn\<close>
  unfolding tuple15_int_assn_def
  apply sepref_to_hoare
  apply vcg
  unfolding ex_tuple15_iff
  apply vcg'
  done

lemma [sepref_frame_match_rules]:
  \<open> hn_ctxt
     (tuple15_assn (invalid_assn a_assn) (invalid_assn b_assn) (invalid_assn c_assn) (invalid_assn d_assn) (invalid_assn e_assn)
    (invalid_assn f_assn) (invalid_assn g_assn) (invalid_assn h_assn) (invalid_assn i_assn) (invalid_assn j_assn) (invalid_assn k_assn)
   (invalid_assn l_assn) (invalid_assn m_assn) (invalid_assn n_assn) (invalid_assn o_assn)) ax bx \<turnstile> hn_val UNIV ax bx\<close>
    unfolding hn_ctxt_def invalid_assn_def tuple15_int_assn_def entails_def
    apply (auto split: prod.split tuple15.splits elim: is_pureE 
      simp: sep_algebra_simps pure_part_pure_conj_eq)
    apply (auto simp: pure_part_def)
      apply (auto simp: pure_def pure_true_conv)
    done

lemma RETURN_case_tuple15_inverse: \<open>RETURN
      (let _ = M
         in ff) =
      (do {_ \<leftarrow> mop_free M;
         RETURN (ff)})\<close>
    by (auto intro!: ext simp: mop_free_def split: tuple15.splits)

sepref_definition update_a_code
  is \<open>uncurry (RETURN oo update_a)\<close>
  :: \<open>a_assn\<^sup>d *\<^sub>a tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a tuple15_int_assn\<close>
  supply [[goals_limit=5]]
  unfolding update_a_def tuple15.case_distrib comp_def RETURN_case_tuple15_inverse
  by sepref

sepref_definition update_b_code
  is \<open>uncurry (RETURN oo update_b)\<close>
  :: \<open>b_assn\<^sup>d *\<^sub>a tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a tuple15_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_b_def tuple15.case_distrib comp_def RETURN_case_tuple15_inverse
  by sepref

sepref_definition update_c_code
  is \<open>uncurry (RETURN oo update_c)\<close>
  :: \<open>c_assn\<^sup>d *\<^sub>a tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a tuple15_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_c_def tuple15.case_distrib comp_def RETURN_case_tuple15_inverse
  by sepref

sepref_definition update_d_code
  is \<open>uncurry (RETURN oo update_d)\<close>
  :: \<open>d_assn\<^sup>d *\<^sub>a tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a tuple15_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_d_def tuple15.case_distrib comp_def RETURN_case_tuple15_inverse
  by sepref

sepref_definition update_e_code
  is \<open>uncurry (RETURN oo update_e)\<close>
  :: \<open>e_assn\<^sup>d *\<^sub>a tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a tuple15_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_e_def tuple15.case_distrib comp_def RETURN_case_tuple15_inverse
  by sepref

sepref_definition update_f_code
  is \<open>uncurry (RETURN oo update_f)\<close>
  :: \<open>f_assn\<^sup>d *\<^sub>a tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a tuple15_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_f_def tuple15.case_distrib comp_def RETURN_case_tuple15_inverse
  by sepref

sepref_definition update_g_code
  is \<open>uncurry (RETURN oo update_g)\<close>
  :: \<open>g_assn\<^sup>d *\<^sub>a tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a tuple15_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_g_def tuple15.case_distrib comp_def RETURN_case_tuple15_inverse
  by sepref

sepref_definition update_h_code
  is \<open>uncurry (RETURN oo update_h)\<close>
  :: \<open>h_assn\<^sup>d *\<^sub>a tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a tuple15_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_h_def tuple15.case_distrib comp_def RETURN_case_tuple15_inverse
  by sepref

sepref_definition update_i_code
  is \<open>uncurry (RETURN oo update_i)\<close>
  :: \<open>i_assn\<^sup>d *\<^sub>a tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a tuple15_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_i_def tuple15.case_distrib comp_def RETURN_case_tuple15_inverse
  by sepref

sepref_definition update_j_code
  is \<open>uncurry (RETURN oo update_j)\<close>
  :: \<open>j_assn\<^sup>d *\<^sub>a tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a tuple15_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_j_def tuple15.case_distrib comp_def RETURN_case_tuple15_inverse
  by sepref

sepref_definition update_k_code
  is \<open>uncurry (RETURN oo update_k)\<close>
  :: \<open>k_assn\<^sup>d *\<^sub>a tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a tuple15_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_k_def tuple15.case_distrib comp_def RETURN_case_tuple15_inverse
  by sepref

sepref_definition update_l_code
  is \<open>uncurry (RETURN oo update_l)\<close>
  :: \<open>l_assn\<^sup>d *\<^sub>a tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a tuple15_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_l_def tuple15.case_distrib comp_def RETURN_case_tuple15_inverse
  by sepref

sepref_definition update_m_code
  is \<open>uncurry (RETURN oo update_m)\<close>
  :: \<open>m_assn\<^sup>d *\<^sub>a tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a tuple15_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_m_def tuple15.case_distrib comp_def RETURN_case_tuple15_inverse
  by sepref

sepref_definition update_n_code
  is \<open>uncurry (RETURN oo update_n)\<close>
  :: \<open>n_assn\<^sup>d *\<^sub>a tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a tuple15_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_n_def tuple15.case_distrib comp_def RETURN_case_tuple15_inverse
  by sepref

sepref_definition update_o_code
  is \<open>uncurry (RETURN oo update_o)\<close>
  :: \<open>o_assn\<^sup>d *\<^sub>a tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a tuple15_int_assn\<close>
  supply [[goals_limit=1]]
  unfolding update_o_def tuple15.case_distrib comp_def RETURN_case_tuple15_inverse
  by sepref

lemma RETURN_case_tuple15_invers: \<open>(RETURN \<circ>\<circ> case_tuple15)
   (\<lambda>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15.
  ff x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15) =
  case_tuple15
   (\<lambda>x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15.
  RETURN (ff x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15))\<close>
  by (auto intro!: ext split: tuple15.splits)

lemmas [sepref_fr_rules] = a b c d e f g h i j k l m n o

sepref_definition remove_a_code
  is \<open>RETURN o remove_a\<close>
  :: \<open> tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a a_assn \<times>\<^sub>a tuple15_int_assn\<close>
  unfolding remove_a_def RETURN_case_tuple15_invers
  by sepref

sepref_definition remove_b_code
  is \<open>RETURN o remove_b\<close>
  :: \<open> tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a b_assn \<times>\<^sub>a tuple15_int_assn\<close>
  unfolding remove_b_def RETURN_case_tuple15_invers
  by sepref

sepref_definition remove_c_code
  is \<open>RETURN o remove_c\<close>
  :: \<open> tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a c_assn \<times>\<^sub>a tuple15_int_assn\<close>
  unfolding remove_c_def RETURN_case_tuple15_invers
  by sepref

sepref_definition remove_d_code
  is \<open>RETURN o remove_d\<close>
  :: \<open> tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a d_assn \<times>\<^sub>a tuple15_int_assn\<close>
  unfolding remove_d_def RETURN_case_tuple15_invers
  by sepref

sepref_definition remove_e_code
  is \<open>RETURN o remove_e\<close>
  :: \<open> tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a e_assn \<times>\<^sub>a tuple15_int_assn\<close>
  unfolding remove_e_def RETURN_case_tuple15_invers
  by sepref

sepref_definition remove_f_code
  is \<open>RETURN o remove_f\<close>
  :: \<open> tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a f_assn \<times>\<^sub>a tuple15_int_assn\<close>
  unfolding remove_f_def RETURN_case_tuple15_invers
  by sepref

sepref_definition remove_g_code
  is \<open>RETURN o remove_g\<close>
  :: \<open> tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a g_assn \<times>\<^sub>a tuple15_int_assn\<close>
  unfolding remove_g_def RETURN_case_tuple15_invers
  by sepref

sepref_definition remove_h_code
  is \<open>RETURN o remove_h\<close>
  :: \<open> tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a h_assn \<times>\<^sub>a tuple15_int_assn\<close>
  unfolding remove_h_def RETURN_case_tuple15_invers
  by sepref

sepref_definition remove_i_code
  is \<open>RETURN o remove_i\<close>
  :: \<open> tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a i_assn \<times>\<^sub>a tuple15_int_assn\<close>
  unfolding remove_i_def RETURN_case_tuple15_invers
  by sepref

sepref_definition remove_j_code
  is \<open>RETURN o remove_j\<close>
  :: \<open> tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a j_assn \<times>\<^sub>a tuple15_int_assn\<close>
  unfolding remove_j_def RETURN_case_tuple15_invers
  by sepref

sepref_definition remove_k_code
  is \<open>RETURN o remove_k\<close>
  :: \<open> tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a k_assn \<times>\<^sub>a tuple15_int_assn\<close>
  unfolding remove_k_def RETURN_case_tuple15_invers
  by sepref

sepref_definition remove_l_code
  is \<open>RETURN o remove_l\<close>
  :: \<open> tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a l_assn \<times>\<^sub>a tuple15_int_assn\<close>
  unfolding remove_l_def RETURN_case_tuple15_invers
  by sepref

sepref_definition remove_m_code
  is \<open>RETURN o remove_m\<close>
  :: \<open> tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a m_assn \<times>\<^sub>a tuple15_int_assn\<close>
  unfolding remove_m_def RETURN_case_tuple15_invers
  by sepref

sepref_definition remove_n_code
  is \<open>RETURN o remove_n\<close>
  :: \<open> tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a n_assn \<times>\<^sub>a tuple15_int_assn\<close>
  unfolding remove_n_def RETURN_case_tuple15_invers
  by sepref

sepref_definition remove_o_code
  is \<open>RETURN o remove_o\<close>
  :: \<open> tuple15_int_assn\<^sup>d \<rightarrow>\<^sub>a o_assn \<times>\<^sub>a tuple15_int_assn\<close>
  unfolding remove_o_def RETURN_case_tuple15_invers
  by sepref

lemmas separation_rules =
  remove_a_code.refine
  remove_b_code.refine
  remove_c_code.refine
  remove_d_code.refine
  remove_e_code.refine
  remove_f_code.refine
  remove_g_code.refine
  remove_h_code.refine
  remove_i_code.refine
  remove_j_code.refine
  remove_k_code.refine
  remove_l_code.refine
  remove_m_code.refine
  remove_n_code.refine
  remove_o_code.refine
  update_a_code.refine
  update_b_code.refine
  update_c_code.refine
  update_d_code.refine
  update_e_code.refine
  update_f_code.refine
  update_g_code.refine
  update_h_code.refine
  update_i_code.refine
  update_j_code.refine
  update_k_code.refine
  update_l_code.refine
  update_m_code.refine
  update_n_code.refine
  update_o_code.refine

lemmas code_rules =
  remove_a_code_def
  remove_b_code_def
  remove_c_code_def
  remove_d_code_def
  remove_e_code_def
  remove_f_code_def
  remove_g_code_def
  remove_h_code_def
  remove_i_code_def
  remove_j_code_def
  remove_k_code_def
  remove_l_code_def
  remove_m_code_def
  remove_n_code_def
  remove_o_code_def
  update_a_code_def
  update_b_code_def
  update_c_code_def
  update_d_code_def
  update_e_code_def
  update_f_code_def
  update_g_code_def
  update_h_code_def
  update_i_code_def
  update_j_code_def
  update_k_code_def
  update_l_code_def
  update_m_code_def
  update_n_code_def
  update_o_code_def

lemmas setter_and_getters_def =
   update_a_def remove_a_def
   update_b_def remove_b_def
   update_c_def remove_c_def
   update_d_def remove_d_def
   update_e_def remove_e_def
   update_f_def remove_f_def
   update_g_def remove_g_def
   update_h_def remove_h_def
   update_i_def remove_i_def
   update_j_def remove_j_def
   update_k_def remove_k_def
   update_l_def remove_l_def
   update_m_def remove_m_def
   update_n_def remove_n_def
   update_o_def remove_o_def

end


context tuple15_state
begin
lemma reconstruct_isasat[sepref_frame_match_rules]:
  \<open>hn_ctxt
     (tuple15_assn (a_assn) (b_assn) (c_assn) (d_assn) (e_assn)
    (f_assn) (g_assn) (h_assn) (i_assn) (j_assn) (k_assn)
   (l_assn) (m_assn) (n_assn) (o_assn)) ax bx \<turnstile> hn_ctxt tuple15_int_assn ax bx\<close>
    unfolding tuple15_int_assn_def
    apply (auto split: prod.split tuple15.splits elim: is_pureE 
      simp: sep_algebra_simps pure_part_pure_conj_eq)
      done

context
  fixes x_assn :: \<open>'r \<Rightarrow> 'q \<Rightarrow> assn\<close> and
    read_all_code :: \<open>'xa \<Rightarrow> 'xb \<Rightarrow> 'xc \<Rightarrow> 'xd \<Rightarrow> 'xe \<Rightarrow> 'xf \<Rightarrow> 'xg \<Rightarrow> 'xh \<Rightarrow> 'xi \<Rightarrow> 'xj \<Rightarrow> 'xk \<Rightarrow> 'xl \<Rightarrow> 'xm \<Rightarrow> 'xn \<Rightarrow> 'xo \<Rightarrow> 'q llM\<close> and
    read_all :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'g \<Rightarrow> 'h \<Rightarrow> 'i \<Rightarrow> 'j \<Rightarrow> 'k \<Rightarrow> 'l \<Rightarrow> 'm \<Rightarrow> 'n \<Rightarrow> 'o \<Rightarrow> 'r nres\<close>
begin

definition read_all_wl_heur_code :: \<open>_\<close> where
  \<open>read_all_wl_heur_code xi = (case xi of
  Tuple15 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 \<Rightarrow>
    read_all_code a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15)\<close>

definition read_all_wl_heur :: \<open>('a, 'b, 'c, 'd, 'e, 'f, 'g, 'h, 'i, 'j,
     'k, 'l, 'm, 'n, 'o) tuple15 \<Rightarrow> _\<close> where
  \<open>read_all_wl_heur tuple15 = (case tuple15 of Tuple15 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15a16 \<Rightarrow>
  read_all a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15a16)\<close>

context
  fixes P
  assumes trail_read[sepref_fr_rules]: \<open>(uncurry14 read_all_code, uncurry14 read_all) \<in>
      [uncurry14 P]\<^sub>a a_assn\<^sup>k *\<^sub>a b_assn\<^sup>k *\<^sub>a c_assn\<^sup>k *\<^sub>a d_assn\<^sup>k *\<^sub>a e_assn\<^sup>k *\<^sub>a f_assn\<^sup>k *\<^sub>a
          g_assn\<^sup>k *\<^sub>a h_assn\<^sup>k *\<^sub>a i_assn\<^sup>k *\<^sub>a j_assn\<^sup>k *\<^sub>a k_assn\<^sup>k *\<^sub>a l_assn\<^sup>k *\<^sub>a
          m_assn\<^sup>k *\<^sub>a n_assn\<^sup>k *\<^sub>a o_assn\<^sup>k \<rightarrow> x_assn\<close>
  notes [[sepref_register_adhoc read_all]]
begin
sepref_definition read_all_wl_heur_code_tmp
  is read_all_wl_heur
  :: \<open>[case_tuple15 P]\<^sub>a tuple15_int_assn\<^sup>k \<rightarrow> x_assn\<close>
   unfolding read_all_wl_heur_def
   by sepref

lemmas read_all_wl_heur_code_refine =
  read_all_wl_heur_code_tmp.refine[unfolded read_all_wl_heur_code_tmp_def
    read_all_wl_heur_code_def[symmetric]]
end

end

end

lemma Mreturn_comp_Tuple15:
  \<open>(Mreturn o\<^sub>1\<^sub>5 Tuple15) a b c d e f g h i j k l m n ko =
  Mreturn (Tuple15 a b c d e f g h i j k l m n ko)\<close>
  by auto

lemma tuple15_free[sepref_frame_free_rules]:
  assumes
  \<open>MK_FREE A freea\<close> \<open>MK_FREE B freeb\<close> \<open>MK_FREE C freec\<close> \<open>MK_FREE D freed\<close>
  \<open>MK_FREE E freee\<close> \<open>MK_FREE F freef\<close> \<open>MK_FREE G freeg\<close> \<open>MK_FREE H freeh\<close>
  \<open>MK_FREE I freei\<close> \<open>MK_FREE J freej\<close> \<open>MK_FREE K freek\<close> \<open>MK_FREE L freel\<close>
  \<open>MK_FREE M freem\<close> \<open>MK_FREE N freen\<close> \<open>MK_FREE KO freeko\<close>
  shows
  \<open>
  MK_FREE (tuple15_assn A B C D E F G H I J K L M N KO) (\<lambda>S. case S of Tuple15 a b c d e f g h i j k l m n ko \<Rightarrow> do\<^sub>M {
  freea a; freeb b; freec c; freed d; freee e; freef f; freeg g; freeh h; freei i; freej j;
  freek k; freel l; freem m; freen n; freeko ko
  })\<close>
  supply [vcg_rules] = assms[THEN MK_FREED]
  apply (rule)+
  apply (clarsimp split: tuple15.splits)
  by vcg'

end
