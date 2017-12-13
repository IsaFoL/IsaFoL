theory Ceta_SAT
  imports CeTA_SAT_Imports.Ceta_SAT_Imports
begin

(*
datatype ('f,'l) lab =
  Lab "('f, 'l) lab" 'l
| FunLab "('f, 'l) lab" "('f, 'l) lab list"
| UnLab 'f
| Sharp "('f, 'l) lab" *)
lemma list_assn_cong:
  \<open>\<lbrakk>\<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> f x y = g x y\<rbrakk> \<Longrightarrow>
      list_assn f xs ys = list_assn g xs ys\<close>
  by (induction f xs ys rule: list_assn.induct) auto

lemma list_assn_fundef_cong[fundef_cong]:
  \<open>\<lbrakk>xs = xs'; ys = ys'; \<And>x y. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> f x y = g x y\<rbrakk> \<Longrightarrow>
      list_assn f xs ys = list_assn g xs' ys'\<close>
  by (auto intro: list_assn_cong)

lemma option_assn_assn_fundef_cong[fundef_cong]:
  \<open>\<lbrakk>xs = xs'; ys = ys'; \<And>x y. x \<in> set_option xs \<Longrightarrow> y \<in> set_option ys \<Longrightarrow> f x y = g x y\<rbrakk> \<Longrightarrow>
      option_assn f xs ys = option_assn g xs' ys'\<close>
  by (auto simp: option_assn_alt_def split: option.splits)

lemma sum_assn_assn_fundef_cong[fundef_cong]:
  \<open>\<lbrakk>xs = xs'; ys = ys';
      \<And>x y. x \<in> Basic_BNFs.setl xs \<Longrightarrow> y \<in> Basic_BNFs.setl ys \<Longrightarrow> f x y = f' x y;
      \<And>x y. x \<in> Basic_BNFs.setr xs \<Longrightarrow> y \<in> Basic_BNFs.setr ys \<Longrightarrow> g x y = g' x y\<rbrakk> \<Longrightarrow>
     (f +\<^sub>a g) xs ys = (f' +\<^sub>a g') xs' ys'\<close>
  by (cases xs; cases ys; cases ys'; cases ys') (auto simp:)

lemma prod_assn_assn_fundef_cong[fundef_cong]:
  \<open>\<lbrakk>xs = xs'; ys = ys'; f (fst xs) (fst ys) = f' (fst xs) (fst ys);
     g (snd xs) (snd ys) = g' (snd xs) (snd ys)\<rbrakk> \<Longrightarrow>
     (f *a g) xs ys = (f' *a g') xs' ys'\<close>
  by (cases xs; cases ys; cases ys'; cases ys') auto

fun lab_assn :: \<open>('f \<Rightarrow> 'g \<Rightarrow> assn) \<Rightarrow> ('l \<Rightarrow> 'm \<Rightarrow> assn) \<Rightarrow> ('f,'l) lab \<Rightarrow> ('g, 'm) lab \<Rightarrow> assn\<close> where
  \<open>lab_assn A B (Lab xs l) (Lab xs' l') = lab_assn A B xs xs' * B l l'\<close> |
  \<open>lab_assn A B (FunLab xs ys) (FunLab xs' ys') = lab_assn A B xs xs' * list_assn (lab_assn A B) ys ys'\<close>|
  \<open>lab_assn A B (UnLab x) (UnLab x') = A x x'\<close> |
  \<open>lab_assn A B (lab.Sharp xs) (lab.Sharp xs') = lab_assn A B xs xs'\<close> |
  \<open>lab_assn _ _ _ _ = false\<close>


term sum_assn
typ "('f, 'l, 'v) trs_termination_proof"

typ "('f, 'l) lab projL"



(* type_synonym 'f status_impl = "(('f \<times> nat) \<times> nat list)list" *)
definition status_impl_assn where
  \<open>status_impl_assn R = list_assn ((R *a nat_assn) *a list_assn nat_assn)\<close>

fun projL_assn :: \<open>('a \<Rightarrow> 'b \<Rightarrow> assn) \<Rightarrow> 'a projL \<Rightarrow> 'b projL \<Rightarrow> assn\<close> where
  \<open>projL_assn R (Projection f) (Projection g) = list_assn ((R *a nat_assn) *a nat_assn) f g\<close>

fun term_assn
  :: \<open>('f \<Rightarrow> 'f' \<Rightarrow> assn) \<Rightarrow> ('g \<Rightarrow> 'g' \<Rightarrow> assn) \<Rightarrow> ('f, 'g) term \<Rightarrow> ('f', 'g') term \<Rightarrow> assn\<close>
where
  \<open>term_assn A B (Var v') (Var v) = B v' v\<close> |
  \<open>term_assn A B (Fun f' v') (Fun f v) = A f' f * list_assn (term_assn A B) v' v\<close> |
  \<open>term_assn A B _ _ = false\<close>

abbreviation rule_assn
  :: \<open>('f \<Rightarrow> 'f' \<Rightarrow> assn) \<Rightarrow> ('g \<Rightarrow> 'g' \<Rightarrow> assn) \<Rightarrow> ('f, 'g) rule \<Rightarrow> ('f', 'g') rule \<Rightarrow> assn\<close>
where
  \<open>rule_assn A B \<equiv> term_assn A B *a term_assn A B\<close>

abbreviation rules_assn
  :: \<open>('f \<Rightarrow> 'f' \<Rightarrow> assn) \<Rightarrow> ('g \<Rightarrow> 'g' \<Rightarrow> assn) \<Rightarrow> ('f, 'g) rules \<Rightarrow> ('f', 'g') rules \<Rightarrow> assn\<close>
where
  \<open>rules_assn A B \<equiv> list_assn (rule_assn A B)\<close>

abbreviation ruleLL_assn
  :: \<open>('f \<Rightarrow> 'f' \<Rightarrow> assn) \<Rightarrow> ('g \<Rightarrow> 'g' \<Rightarrow> assn) \<Rightarrow> ('h \<Rightarrow> 'h' \<Rightarrow> assn) \<Rightarrow>
        ('f, 'g, 'h) ruleLL \<Rightarrow> ('f', 'g', 'h') ruleLL \<Rightarrow> assn\<close>
where
  \<open>ruleLL_assn A B C \<equiv> rule_assn (lab_assn A B) C\<close>

abbreviation trsLL_assn
  :: \<open>('f \<Rightarrow> 'f' \<Rightarrow> assn) \<Rightarrow> ('g \<Rightarrow> 'g' \<Rightarrow> assn) \<Rightarrow> ('h \<Rightarrow> 'h' \<Rightarrow> assn) \<Rightarrow>
        ('f, 'g, 'h) trsLL \<Rightarrow> ('f', 'g', 'h') trsLL \<Rightarrow> assn\<close>
where
  \<open>trsLL_assn A B C \<equiv> rules_assn (lab_assn A B) C\<close>

abbreviation termsLL_assn
  :: \<open>('f \<Rightarrow> 'f' \<Rightarrow> assn) \<Rightarrow> ('g \<Rightarrow> 'g' \<Rightarrow> assn) \<Rightarrow> ('h \<Rightarrow> 'h' \<Rightarrow> assn) \<Rightarrow>
        ('f, 'g, 'h) termsLL \<Rightarrow> ('f', 'g', 'h') termsLL \<Rightarrow> assn\<close>
where
  \<open>termsLL_assn A B C \<equiv> list_assn (term_assn (lab_assn A B) C)\<close>

abbreviation pos_assn :: \<open>pos \<Rightarrow> pos \<Rightarrow> assn\<close> where
  \<open>pos_assn \<equiv> id_assn\<close>

abbreviation rseq_assn
  :: \<open>('f \<Rightarrow> 'f' \<Rightarrow> assn) \<Rightarrow> ('g \<Rightarrow> 'g' \<Rightarrow> assn) \<Rightarrow>
        ('f, 'g) rseq \<Rightarrow> ('f', 'g') rseq \<Rightarrow> assn\<close>
where
  \<open>rseq_assn A B \<equiv> list_assn (pos_assn *a rule_assn A B *a term_assn A B)\<close>

abbreviation rseqL_assn
  :: \<open>('f \<Rightarrow> 'f' \<Rightarrow> assn) \<Rightarrow> ('g \<Rightarrow> 'g' \<Rightarrow> assn) \<Rightarrow>  ('h \<Rightarrow> 'h' \<Rightarrow> assn) \<Rightarrow>
        ('f, 'g, 'h) rseqL \<Rightarrow> ('f', 'g', 'h') rseqL \<Rightarrow> assn\<close>
where
  \<open>rseqL_assn A B C \<equiv> list_assn (rule_assn (lab_assn A B) C *a rseq_assn (lab_assn A B) C)\<close>

(*
type_synonym ('f, 'v) rule = "('f, 'v) term \<times> ('f, 'v) term"
type_synonym ('f, 'l, 'v) ruleLL  = "(('f, 'l) lab, 'v) rule"
type_synonym ('f, 'v) rules = "('f, 'v) rule list"
type_synonym ('f, 'l, 'v) trsLL   = "(('f, 'l) lab, 'v) rules"
type_synonym ('f, 'l, 'v) termsLL = "(('f, 'l) lab, 'v) term list"
type_synonym  ('f, 'v) rseq = "(pos \<times> ('f, 'v) rule \<times> ('f, 'v) term) list"
type_synonym ('f, 'l, 'v) rseqL   = "((('f, 'l) lab, 'v) rule \<times> (('f, 'l) lab, 'v) rseq) list"
 *)

abbreviation list_order_type_assn :: \<open>list_order_type \<Rightarrow> list_order_type \<Rightarrow> assn\<close> where
  \<open>list_order_type_assn \<equiv> id_assn\<close>

abbreviation redtriple_impl_assn :: \<open>'f redtriple_impl \<Rightarrow> 'f redtriple_impl \<Rightarrow> assn\<close> where
  \<open>redtriple_impl_assn \<equiv> id_assn\<close>

abbreviation scnp_af_assn :: \<open>('f \<Rightarrow> 'f' \<Rightarrow> assn) \<Rightarrow> 'f scnp_af \<Rightarrow> 'f' scnp_af \<Rightarrow> assn\<close> where
  \<open>scnp_af_assn A \<equiv> list_assn ((A *a nat_assn) *a list_assn (nat_assn *a nat_assn))\<close>

fun root_redtriple_impl_assn :: \<open>'f root_redtriple_impl \<Rightarrow> 'f root_redtriple_impl \<Rightarrow> assn\<close> where
  \<open>root_redtriple_impl_assn (SCNP a b c) (SCNP a' b' c') =
       list_order_type_assn a a' * scnp_af_assn id_assn b b' * redtriple_impl_assn c c'\<close>
(*
type_synonym 'f scnp_af = "(('f \<times> nat) \<times> (nat \<times> nat) list) list"
datatype ('f) root_redtriple_impl = SCNP list_order_type "'f scnp_af" "'f redtriple_impl"
 *)

function
   dp_termination_proof_assn  ::
      "('e, 'f, 'g) dp_termination_proof \<Rightarrow> ('e, 'f, 'g) dp_termination_proof \<Rightarrow> assn" and
   trs_termination_proof_assn ::
     "('e, 'f, 'g) trs_termination_proof \<Rightarrow> ('e, 'f, 'g) trs_termination_proof \<Rightarrow> assn"
   where
     \<open>dp_termination_proof_assn a b = (case (a, b) of
     (P_is_Empty, P_is_Empty) \<Rightarrow> true
  | (Subterm_Criterion_Proc projL rseqL trsLL term,
       Subterm_Criterion_Proc projL' rseqL' trsLL' term') \<Rightarrow>
    projL_assn (lab_assn id_assn id_assn) projL projL' *
    rseqL_assn id_assn id_assn id_assn  rseqL rseqL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term'
  | (Gen_Subterm_Criterion_Proc projL trsLL term,
      Gen_Subterm_Criterion_Proc projL' trsLL' term') \<Rightarrow>
    status_impl_assn (lab_assn id_assn id_assn) projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term'
  | (Redpair_Proc projL trsLL term, Redpair_Proc projL' trsLL' term') \<Rightarrow>
    (root_redtriple_impl_assn +\<^sub>a redtriple_impl_assn) projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term'
  | (Redpair_UR_Proc projL trsLL trsLL2 term, Redpair_UR_Proc projL' trsLL' trsLL2' term') \<Rightarrow>
    (root_redtriple_impl_assn +\<^sub>a redtriple_impl_assn) projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    dp_termination_proof_assn term term'
  | (Usable_Rules_Proc trsLL term, Usable_Rules_Proc trsLL' term') \<Rightarrow>
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term'
  | (Dep_Graph_Proc term, Dep_Graph_Proc term') \<Rightarrow>
    list_assn (option_assn dp_termination_proof_assn *a
      trsLL_assn id_assn id_assn id_assn) term term'
  | (Mono_Redpair_Proc projL trsLL trsLL2 term,
      Mono_Redpair_Proc projL' trsLL' trsLL2' term') \<Rightarrow>
    redtriple_impl_assn projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    dp_termination_proof_assn term term'
  | (Mono_URM_Redpair_Proc projL trsLL trsLL2 term,
      Mono_URM_Redpair_Proc projL' trsLL' trsLL2' term') \<Rightarrow>
    redtriple_impl_assn projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    dp_termination_proof_assn term term'
  | (Mono_Redpair_UR_Proc projL trsLL trsLL2 trsLL3 term,
      Mono_Redpair_UR_Proc projL' trsLL' trsLL2' trsLL3' term') \<Rightarrow>
    id_assn projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    trsLL_assn id_assn id_assn id_assn trsLL3 trsLL3' *
    dp_termination_proof_assn term term'
  | (Size_Change_Subterm_Proc term,
      Size_Change_Subterm_Proc term') \<Rightarrow>
    list_assn (rule_assn (lab_assn id_assn id_assn) id_assn *a
       list_assn (nat_assn *a nat_assn) *a list_assn (nat_assn *a nat_assn)) term term'
  | (Size_Change_Redpair_Proc red trsLL term,
      Size_Change_Redpair_Proc red' trsLL' term') \<Rightarrow>
    redtriple_impl_assn red red' * option_assn (trsLL_assn id_assn id_assn id_assn) trsLL trsLL' *
    list_assn (rule_assn (lab_assn id_assn id_assn) id_assn *a
       list_assn (nat_assn *a nat_assn) *a list_assn (nat_assn *a nat_assn)) term term'
  | (Uncurry_Proc n unc trsLL2 trsLL3 term,
      Uncurry_Proc n' unc' trsLL2' trsLL3' term') \<Rightarrow>
    option_assn nat_assn n n' *
    id_assn unc unc' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    trsLL_assn id_assn id_assn id_assn trsLL3 trsLL3' *
    dp_termination_proof_assn term term'
  | (Fcc_Proc n unc trsLL2 trsLL3 term,
      Fcc_Proc n' unc' trsLL2' trsLL3' term') \<Rightarrow>
    lab_assn id_assn id_assn n n' *
    id_assn unc unc' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    trsLL_assn id_assn id_assn id_assn trsLL3 trsLL3' *
    dp_termination_proof_assn term term'
  | (Split_Proc trsLL trsLL2 term term2,
      Split_Proc trsLL' trsLL2' term' term2') \<Rightarrow>
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    dp_termination_proof_assn term term' *
    dp_termination_proof_assn term2 term2'
  | (Semlab_Proc sl  trsLL2 unc trsLL3 term,
      Semlab_Proc sl' trsLL2' unc' trsLL3' term') \<Rightarrow>
    id_assn sl sl' *
    list_assn (term_assn id_assn id_assn) unc unc' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    trsLL_assn id_assn id_assn id_assn trsLL3 trsLL3' *
    dp_termination_proof_assn term term'
  | (Switch_Innermost_Proc sl term,
      Switch_Innermost_Proc sl' term') \<Rightarrow>
    id_assn sl sl' *
    dp_termination_proof_assn term term'
  | (Rewriting_Proc n r1 r2 r3 r4 apos term,
      Rewriting_Proc n' r1' r2' r3' r4' apos' term') \<Rightarrow>
    option_assn (trsLL_assn id_assn id_assn id_assn) n n' *
    ruleLL_assn id_assn id_assn id_assn r1 r1' *
    ruleLL_assn id_assn id_assn id_assn r2 r2' *
    ruleLL_assn id_assn id_assn id_assn r3 r3' *
    ruleLL_assn id_assn id_assn id_assn r4 r4' *
    dp_termination_proof_assn term term'
  | (Instantiation_Proc r1 trsLL term,
      Instantiation_Proc r1' trsLL' term') \<Rightarrow>
    ruleLL_assn id_assn id_assn id_assn r1 r1' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term'
  | (Forward_Instantiation_Proc r1 trsLL trsLL2 term,
      Forward_Instantiation_Proc r1' trsLL' trsLL2' term') \<Rightarrow>
    ruleLL_assn id_assn id_assn id_assn r1 r1' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    option_assn (trsLL_assn id_assn id_assn id_assn) trsLL2 trsLL2' *
    dp_termination_proof_assn term term'
  | (Narrowing_Proc r1 apos trsLL term,
      Narrowing_Proc r1' apos' trsLL' term') \<Rightarrow>
    ruleLL_assn id_assn id_assn id_assn r1 r1' *
    pos_assn apos apos' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term'
  | (Assume_Finite r1 term,
      Assume_Finite r1' term') \<Rightarrow>
    id_assn r1 r1' *
    id_assn term term'  (* cheating *)
  | (Unlab_Proc trsLL trsLL2 term,
      Unlab_Proc trsLL' trsLL2' term') \<Rightarrow>
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    dp_termination_proof_assn term term'
  | (Q_Reduction_Proc trsLL term,
      Q_Reduction_Proc trsLL' term') \<Rightarrow>
    termsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term'
  | (Complex_Constant_Removal_Proc trsLL term,
      Complex_Constant_Removal_Proc trsLL' term') \<Rightarrow>
    id_assn trsLL trsLL' *
    dp_termination_proof_assn term term'
  | (General_Redpair_Proc red trsLL trsLL2 p term,
      General_Redpair_Proc red' trsLL' trsLL2' p' term') \<Rightarrow>
    redtriple_impl_assn red red' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    id_assn p p' *
    list_assn dp_termination_proof_assn term term'
  | (To_Trs_Proc red, To_Trs_Proc red') \<Rightarrow>
    trs_termination_proof_assn red red'
  | (_, _) \<Rightarrow> false)\<close> |
\<open>trs_termination_proof_assn a b =
   (case (a, b) of
   (DP_Trans b1 b2 r dp, DP_Trans b1' b2' r' dp') \<Rightarrow>
     bool_assn b1 b1' * bool_assn b2 b2' *
     rules_assn id_assn id_assn r r' *
     dp_termination_proof_assn dp dp'
  | (Rule_Removal r trsLL ts, Rule_Removal r' trsLL' ts') \<Rightarrow>
     redtriple_impl_assn r r' *
     trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
     trs_termination_proof_assn ts ts'
  | (String_Reversal ts, String_Reversal ts') \<Rightarrow>
     trs_termination_proof_assn ts ts'
  | (Constant_String a ts, Constant_String a' ts') \<Rightarrow>
     id_assn a a' *
     trs_termination_proof_assn ts ts'
  | (Bounds a, Bounds a') \<Rightarrow>  id_assn a a'
  | (Uncurry unc trsLL2  ts, Uncurry unc' trsLL2' ts') \<Rightarrow>
     id_assn unc unc' *
     trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
     trs_termination_proof_assn ts ts'
  | (Semlab sl term trsLL ts, Semlab sl' term' trsLL' ts') \<Rightarrow>
     id_assn sl sl' *
     list_assn (term_assn id_assn id_assn) term term' *
     trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
     trs_termination_proof_assn ts ts'
  | (R_is_Empty, R_is_Empty) \<Rightarrow> true
  | (Fcc sl trsLL ts, Fcc sl' trsLL' ts') \<Rightarrow>
     id_assn sl sl' *
     trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
     trs_termination_proof_assn ts ts'
  | (Split trsLL ts1 ts2, Split trsLL' ts1' ts2') \<Rightarrow>
     trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
     trs_termination_proof_assn ts1 ts1' *
     trs_termination_proof_assn ts2 ts2'
  | (Switch_Innermost sl ts, Switch_Innermost sl' ts') \<Rightarrow>
     id_assn sl sl' *
     trs_termination_proof_assn ts ts'
  | (Drop_Equality ts, Drop_Equality ts') \<Rightarrow>
     trs_termination_proof_assn ts ts'
  | (Remove_Nonapplicable_Rules trsLL ts1, Remove_Nonapplicable_Rules trsLL' ts1') \<Rightarrow>
     trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
     trs_termination_proof_assn ts1 ts1'
  | (Permuting_AFS trsLL ts1, Permuting_AFS trsLL' ts1') \<Rightarrow>
     id_assn trsLL trsLL' *
     trs_termination_proof_assn ts1 ts1'
  | (Assume_SN trsLL ts1, Assume_SN trsLL' ts1') \<Rightarrow>
     id_assn trsLL trsLL' *
     id_assn ts1 ts1'
  | (_, _) \<Rightarrow> false)\<close>
  by pat_completeness (auto; fail)+
termination
  by (lexicographic_order)

end