theory Ceta_SAT
  imports CeTA_SAT_Imports.Ceta_SAT_Imports
begin

(* to avoid ambiguities and exponentially many parse trees *)
no_notation vec_nth (infixl "$" 90)
no_notation vec_index (infixl "$" 100)

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

abbreviation qreltrsLL_assn:: \<open>('f, 'l, 'v) qreltrsLL \<Rightarrow> ('f, 'l, 'v) qreltrsLL \<Rightarrow> assn\<close> where
\<open>qreltrsLL_assn \<equiv> id_assn\<close>

abbreviation assm_proof_assn 
  :: \<open>('f,'l,'v,('f, 'l, 'v) trs_termination_proof,('f, 'l, 'v) dp_termination_proof,
       ('f, 'l, 'v) fptrs_termination_proof,('f, 'l, 'v) unknown_proof) assm_proof \<Rightarrow> 
     ('f,'l,'v,('f, 'l, 'v) trs_termination_proof,('f, 'l, 'v) dp_termination_proof,
       ('f, 'l, 'v) fptrs_termination_proof,('f, 'l, 'v) unknown_proof) assm_proof \<Rightarrow> assn\<close>
where
  \<open>assm_proof_assn \<equiv> id_assn\<close>

abbreviation list_assm_proof_assn
  :: \<open>('f,'l,'v,('f, 'l, 'v) trs_termination_proof,('f, 'l, 'v) dp_termination_proof,
       ('f, 'l, 'v) fptrs_termination_proof,('f, 'l, 'v) unknown_proof) assm_proof list \<Rightarrow> 
     ('f,'l,'v,('f, 'l, 'v) trs_termination_proof,('f, 'l, 'v) dp_termination_proof,
       ('f, 'l, 'v) fptrs_termination_proof,('f, 'l, 'v) unknown_proof) assm_proof list \<Rightarrow> assn\<close>
where
  \<open>list_assm_proof_assn \<equiv> list_assn assm_proof_assn\<close>

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
     qreltrsLL_assn trsLL trsLL' *
     list_assm_proof_assn ts1 ts1'
  | (_, _) \<Rightarrow> false)\<close>
  by pat_completeness (auto; fail)+
termination
  by (lexicographic_order)

abbreviation (input)ABS3 :: "('a\<Rightarrow>'b\<Rightarrow>'c)\<Rightarrow>'a\<Rightarrow>'b\<Rightarrow>'c" (binder "\<lambda>\<^sub>3" 10)
  where "ABS3 f \<equiv> (\<lambda>x y. PROTECT2 (f x y) DUMMY)"

abbreviation (input)ABS4 :: "('a\<Rightarrow>'b\<Rightarrow>'c\<Rightarrow>'d)\<Rightarrow>'a\<Rightarrow>'b\<Rightarrow>'c\<Rightarrow>'d" (binder "\<lambda>\<^sub>4" 10)
  where "ABS4 f \<equiv> (\<lambda>x y z. PROTECT2 (f x y z) DUMMY)"

abbreviation (input)ABS5 :: "('a\<Rightarrow>'b\<Rightarrow>'c\<Rightarrow>'d\<Rightarrow>'e)\<Rightarrow>'a\<Rightarrow>'b\<Rightarrow>'c\<Rightarrow>'d\<Rightarrow>'e" (binder "\<lambda>\<^sub>5" 10)
  where "ABS5 f \<equiv> (\<lambda>x y z a. PROTECT2 (f x y z a) DUMMY)"

abbreviation (input)ABS6 :: "('a\<Rightarrow>'b\<Rightarrow>'c\<Rightarrow>'d\<Rightarrow>'e\<Rightarrow>'f)\<Rightarrow>'a\<Rightarrow>'b\<Rightarrow>'c\<Rightarrow>'d\<Rightarrow>'e\<Rightarrow>'f" (binder "\<lambda>\<^sub>6" 10)
  where "ABS6 f \<equiv> (\<lambda>x y z a b. PROTECT2 (f x y z a b) DUMMY)"

abbreviation (input)ABS7 :: "('a\<Rightarrow>'b\<Rightarrow>'c\<Rightarrow>'d\<Rightarrow>'e\<Rightarrow>'f\<Rightarrow>'g)\<Rightarrow>'a\<Rightarrow>'b\<Rightarrow>'c\<Rightarrow>'d\<Rightarrow>'e\<Rightarrow>'f\<Rightarrow>'g" (binder "\<lambda>\<^sub>7" 10)
  where "ABS7 f \<equiv> (\<lambda>x y z a b c. PROTECT2 (f x y z a b c) DUMMY)"

abbreviation (input)ABS8 :: "('a\<Rightarrow>'b\<Rightarrow>'c\<Rightarrow>'d\<Rightarrow>'e\<Rightarrow>'f\<Rightarrow>'g\<Rightarrow>'h)\<Rightarrow>'a\<Rightarrow>'b\<Rightarrow>'c\<Rightarrow>'d\<Rightarrow>'e\<Rightarrow>'f\<Rightarrow>'g\<Rightarrow>'h" (binder "\<lambda>\<^sub>8" 10)
  where "ABS8 f \<equiv> (\<lambda>x y z a b c d. PROTECT2 (f x y z a b c d) DUMMY)"


declare trs_termination_proof_assn.simps[simp del] dp_termination_proof_assn.simps[simp del]

lemma hn_trs_termination_proof_assn:
    "trs_termination_proof_assn x y = z \<Longrightarrow> hn_ctxt (trs_termination_proof_assn) x y = z"
  by (simp add: hn_ctxt_def)

lemma entt_fr_drop': \<open>F \<Longrightarrow>\<^sub>t F' \<Longrightarrow> A * F \<Longrightarrow>\<^sub>t F'\<close>
  using assn_times_comm entt_fr_drop by fastforce

method hn_case_proof uses ccase merge =
  (rule hn_refine_cons[OF _ ccase _ entt_refl],
   solves \<open>simp add: assn_times_comm entt_fr_drop\<close>,
   assumption,
   assumption,
   rule entt_star_mono,
     rule entt_fr_drop,
     solves \<open>simp add: hn_ctxt_def trs_termination_proof_assn.simps\<close>,
  rule entt_trans[OF _ merge],
  solves \<open>simp add: entt_disjI1' entt_disjI2'\<close>)


lemma hn_case_trs_termination_proof_assn[sepref_prep_comb_rule, sepref_comb_rules]:
  fixes p p' P
  defines [simp]: "INVE \<equiv> hn_invalid (trs_termination_proof_assn) p p'"
  assumes FR: "\<Gamma> \<Longrightarrow>\<^sub>t hn_ctxt (trs_termination_proof_assn) p p' * F"
  assumes DP_Trans:
    "\<And>b1 b2 r dp b1' b2' r' dp'. \<lbrakk> p=DP_Trans b1 b2 r dp; p'=DP_Trans b1' b2' r' dp'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f1' b1' b2' r' dp')
       (bool_assn b1 b1' * bool_assn b2 b2' *
         rules_assn id_assn id_assn r r' *
         dp_termination_proof_assn dp dp' * hn_ctxt XX1 p p' * \<Gamma>2') R (f1 b1 b2 r dp)"
  assumes Rule_Removal:
    "\<And>r trsLL ts r' trsLL' ts'. \<lbrakk> p=Rule_Removal r trsLL ts; p'=Rule_Removal r' trsLL' ts'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f2' r' trsLL' ts')
       (redtriple_impl_assn r r' *  trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
        trs_termination_proof_assn ts ts' * hn_ctxt XX2 p p' * \<Gamma>2') R (f2 r trsLL ts)"
  assumes String_Reversal:
    "\<And>ts ts'. \<lbrakk> p=String_Reversal ts; p'=String_Reversal ts'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f3' ts')
       (trs_termination_proof_assn ts ts' * hn_ctxt XX3 p p' * \<Gamma>3') R (f3 ts)"
  assumes Constant_String:
    "\<And>a ts a' ts'. \<lbrakk> p=Constant_String a ts; p'=Constant_String a' ts'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f4' a' ts')
       (id_assn a a' * trs_termination_proof_assn ts ts' * hn_ctxt XX4 p p' * \<Gamma>4') R (f4 a ts)"
  assumes Bounds:
    "\<And>ts ts'. \<lbrakk> p=Bounds ts; p'=Bounds ts'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f5' ts')
       (id_assn ts ts' * hn_ctxt XX5 p p' * \<Gamma>5') R (f5 ts)"
  assumes Uncurry:
    "\<And>unc trsLL2 ts unc' trsLL2' ts'. \<lbrakk> p=Uncurry unc trsLL2 ts; p'=Uncurry unc' trsLL2' ts'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f6' unc' trsLL2' ts')
       (id_assn unc unc' * trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
       trs_termination_proof_assn ts ts' * hn_ctxt XX6 p p' * \<Gamma>6') R (f6 unc trsLL2 ts)"
  assumes Semlab:
    "\<And>sl term trsLL ts sl' term' trsLL' ts'. \<lbrakk> p=Semlab sl term trsLL ts; p'=Semlab sl' term' trsLL' ts'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f7' sl' term' trsLL' ts')
       (id_assn sl sl' *
       list_assn (term_assn id_assn id_assn) term term' *
       trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
     trs_termination_proof_assn ts ts' * hn_ctxt XX7 p p' * \<Gamma>7') R (f7 sl term trsLL ts)"
  assumes R_is_Empty: "p=R_is_Empty \<Longrightarrow> hn_refine (hn_ctxt (trs_termination_proof_assn) p p' * F) f8'
        (hn_ctxt XX8 p p' * \<Gamma>8') R f8"
  assumes Fcc:
    "\<And>sl trsLL ts sl' trsLL' ts'. \<lbrakk> p=Fcc sl trsLL ts; p'=Fcc sl' trsLL' ts'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f9' sl' trsLL' ts')
       (id_assn sl sl' *
       trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
     trs_termination_proof_assn ts ts' * hn_ctxt XX9 p p' * \<Gamma>9') R (f9 sl trsLL ts)"
  assumes Split:
    "\<And>trsLL ts1 ts2 sl' trsLL' ts1' ts2'. \<lbrakk> p=Split trsLL ts1 ts2; p'=Split trsLL' ts1' ts2'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f10' trsLL' ts1' ts2')
       (trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
     trs_termination_proof_assn ts1 ts1' *
     trs_termination_proof_assn ts2 ts2' * hn_ctxt XX10 p p' * \<Gamma>10') R (f10 trsLL ts1 ts2)"
  assumes Switch_Innermost:
    "\<And>sl ts sl' ts'. \<lbrakk> p=Switch_Innermost sl ts; p'=Switch_Innermost sl' ts'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f11' sl' ts')
       (id_assn sl sl' * trs_termination_proof_assn ts ts' * hn_ctxt XX11 p p' * \<Gamma>11') R (f11 sl ts)"
  assumes Drop_Equality:
    "\<And>ts ts'. \<lbrakk> p=Drop_Equality ts; p'=Drop_Equality ts'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f12' ts')
       (trs_termination_proof_assn ts ts' * hn_ctxt XX12 p p' * \<Gamma>12') R (f12 ts)"
  assumes Remove_Nonapplicable_Rules:
    "\<And>trsLL ts1 trsLL' ts1'. \<lbrakk> p=Remove_Nonapplicable_Rules trsLL ts1; p'=Remove_Nonapplicable_Rules trsLL' ts1'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f13' trsLL' ts1')
       (trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
     trs_termination_proof_assn ts1 ts1' * hn_ctxt XX13 p p' * \<Gamma>13') R (f13 trsLL ts1)"
  assumes Permuting_AFS:
    "\<And>trsLL ts1 trsLL' ts1'. \<lbrakk> p=Permuting_AFS trsLL ts1; p'=Permuting_AFS trsLL' ts1'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f14' trsLL' ts1')
       (id_assn trsLL trsLL' * trs_termination_proof_assn ts1 ts1' * hn_ctxt XX14 p p' * \<Gamma>14') R (f14 trsLL ts1)"
  assumes Assume_SN:
    "\<And>trsLL ts1 trsLL' ts1'. \<lbrakk> p=Assume_SN trsLL ts1; p'=Assume_SN trsLL' ts1'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f15' trsLL' ts1')
       (qreltrsLL_assn trsLL trsLL' * list_assm_proof_assn ts1 ts1' * hn_ctxt XX15 p p' * \<Gamma>15') R (f15 trsLL ts1)"
  assumes MERGE1: "\<Gamma>1' \<or>\<^sub>A \<Gamma>2' \<or>\<^sub>A \<Gamma>3' \<or>\<^sub>A \<Gamma>4'  \<or>\<^sub>A \<Gamma>5' \<or>\<^sub>A \<Gamma>6' \<or>\<^sub>A \<Gamma>7' \<or>\<^sub>A \<Gamma>8' \<or>\<^sub>A \<Gamma>9' \<or>\<^sub>A \<Gamma>10' \<or>\<^sub>A
         \<Gamma>11' \<or>\<^sub>A \<Gamma>12' \<or>\<^sub>A \<Gamma>13' \<or>\<^sub>A \<Gamma>14' \<or>\<^sub>A \<Gamma>15' \<Longrightarrow>\<^sub>t \<Gamma>'"
  shows
    "hn_refine \<Gamma>
      (case_trs_termination_proof f1' f2' f3' f4' f5' f6' f7' f8' f9' f10' f11' f12' f13' f14' f15' p')
      (hn_ctxt (trs_termination_proof_assn) p p' * \<Gamma>') R
      (case_trs_termination_proof$ABS5 f1$ABS4 f2$ABS2 f3$ABS3 f4$ABS2 f5$ABS4 f6$ABS5 f7$f8$
       ABS4 f9$ABS4 f10$ABS3 f11$ABS2 f12$ABS3 f13$ABS3 f14$ABS3 f15$p)"
  supply [[goals_limit=1]]
  apply (rule hn_refine_cons_pre[OF FR])
  apply1 extract_hnr_invalids
  apply (subst trs_termination_proof_assn.simps[THEN hn_trs_termination_proof_assn])
  apply (cases p; cases p'; simp add:)
  subgoal by (hn_case_proof ccase:DP_Trans merge:MERGE1)
  subgoal by (hn_case_proof ccase:Rule_Removal merge:MERGE1)
  subgoal by (hn_case_proof ccase:String_Reversal merge:MERGE1)
  subgoal by (hn_case_proof ccase:Constant_String merge:MERGE1)
  subgoal by (hn_case_proof ccase:Bounds merge:MERGE1)
  subgoal by (hn_case_proof ccase:Uncurry merge:MERGE1)
  subgoal by (hn_case_proof ccase:Semlab merge:MERGE1)
  subgoal
    apply (rule hn_refine_cons[OF _ R_is_Empty _ entt_refl]; assumption?)
     applyS (simp add: hn_ctxt_def trs_termination_proof_assn.simps)
    apply (simp add: hn_ctxt_def trs_termination_proof_assn.simps)
    apply1 (rule entt_trans[OF _ MERGE1])
    applyS (simp add: entt_disjI1' entt_disjI2' entt_fr_drop')
    done
  subgoal by (hn_case_proof ccase:Fcc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Split merge:MERGE1)
  subgoal by (hn_case_proof ccase:Switch_Innermost merge:MERGE1)
  subgoal by (hn_case_proof ccase:Drop_Equality merge:MERGE1)
  subgoal by (hn_case_proof ccase:Remove_Nonapplicable_Rules merge:MERGE1)
  subgoal by (hn_case_proof ccase:Permuting_AFS merge:MERGE1)
  subgoal by (hn_case_proof ccase:Assume_SN merge:MERGE1)
  done

declare dp_termination_proof_assn.simps[simp del]

lemma hn_dp_termination_proof_assn:
    "dp_termination_proof_assn x y = z \<Longrightarrow> hn_ctxt (dp_termination_proof_assn) x y = z"
  by (simp add: hn_ctxt_def)

method hn_case_proof_internal uses ccase merge =
  (rule hn_refine_cons[OF _ ccase _ entt_refl],
   solves \<open>simp add: assn_times_comm entt_fr_drop\<close>,
   assumption,
   assumption,
   rule entt_star_mono,
     rule entt_fr_drop,
     subst dp_termination_proof_assn.simps[THEN hn_dp_termination_proof_assn],
     solves \<open>simp add: hn_ctxt_def\<close>,
  rule entt_trans[OF _ merge],
  solves \<open>simp add: entt_disjI1' entt_disjI2'\<close>)

method hn_case_proof uses ccase merge =
  (hn_case_proof_internal ccase:ccase merge:merge; fail)

lemma hn_case_dp_termination_proof_assn[sepref_prep_comb_rule, sepref_comb_rules]:
  fixes p p' P
  defines [simp]: "INVE \<equiv> hn_invalid (dp_termination_proof_assn) p p'"
  assumes FR: "\<Gamma> \<Longrightarrow>\<^sub>t hn_ctxt (dp_termination_proof_assn) p p' * F"
  assumes P_is_Empty: "p=P_is_Empty \<Longrightarrow>
      hn_refine (hn_ctxt (dp_termination_proof_assn) p p' * F) f1'
        (hn_ctxt XX1 p p' * \<Gamma>1') R f1"
 assumes Subterm_Criterion_Proc:
    "\<And>projL rseqL trsLL term projL' rseqL' trsLL' term'. \<lbrakk>p=Subterm_Criterion_Proc projL rseqL trsLL term;
       p'= Subterm_Criterion_Proc projL' rseqL' trsLL' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f2' projL' rseqL' trsLL' term')
       (projL_assn (lab_assn id_assn id_assn) projL projL' *
    rseqL_assn id_assn id_assn id_assn  rseqL rseqL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term' * hn_ctxt XX2 p p' * \<Gamma>2') R (f2 projL rseqL trsLL term)"
 assumes Gen_Subterm_Criterion_Proc:
    "\<And>projL rseqL trsLL term projL' trsLL' term'. \<lbrakk>p=Gen_Subterm_Criterion_Proc projL trsLL term;
       p'= Gen_Subterm_Criterion_Proc projL' trsLL' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f3' projL' trsLL' term')
       (status_impl_assn (lab_assn id_assn id_assn) projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term' * hn_ctxt XX3 p p' * \<Gamma>3') R (f3 projL trsLL term)"
 assumes Redpair_Proc:
    "\<And> projL trsLL term projL' trsLL' term'. \<lbrakk>p=Redpair_Proc projL trsLL term;
       p'= Redpair_Proc projL' trsLL' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f4' projL' trsLL' term')
       ((root_redtriple_impl_assn +\<^sub>a redtriple_impl_assn) projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term' * hn_ctxt XX4 p p' * \<Gamma>4') R (f4 projL trsLL term)"
 assumes Redpair_UR_Proc:
    "\<And> projL trsLL trsLL2 term  projL' trsLL' trsLL2' term'. \<lbrakk>p=Redpair_UR_Proc projL trsLL trsLL2 term;
       p'= Redpair_UR_Proc  projL' trsLL' trsLL2' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f5' projL' trsLL' trsLL2' term')
       ((root_redtriple_impl_assn +\<^sub>a redtriple_impl_assn) projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    dp_termination_proof_assn term term' * hn_ctxt XX5 p p' * \<Gamma>5') R (f5 projL trsLL trsLL2 term)"
 assumes Usable_Rules_Proc:
    "\<And>trsLL term trsLL' term'. \<lbrakk>p=Usable_Rules_Proc trsLL term;
       p'= Usable_Rules_Proc trsLL' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f6' trsLL' term')
       (trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term' * hn_ctxt XX6 p p' * \<Gamma>6') R (f6 trsLL term)"
 assumes Dep_Graph_Proc:
    "\<And>term term'. \<lbrakk>p=Dep_Graph_Proc term;
       p'= Dep_Graph_Proc term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f7' term')
       (list_assn (option_assn dp_termination_proof_assn *a
      trsLL_assn id_assn id_assn id_assn) term term' * hn_ctxt XX7 p p' * \<Gamma>7') R (f7 term)"
 assumes Mono_Redpair_Proc:
    "\<And>projL trsLL trsLL2 term projL' trsLL' trsLL2' term'. \<lbrakk>p=Mono_Redpair_Proc projL trsLL trsLL2 term;
       p'= Mono_Redpair_Proc projL' trsLL' trsLL2' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f8' projL' trsLL' trsLL2' term')
       (redtriple_impl_assn projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    dp_termination_proof_assn term term' * hn_ctxt XX8 p p' * \<Gamma>8') R (f8 projL trsLL trsLL2 term)"
assumes Mono_URM_Redpair_Proc:
    "\<And>projL trsLL trsLL2 term projL' trsLL' trsLL2' term'. \<lbrakk>p=Mono_URM_Redpair_Proc projL trsLL trsLL2 term;
       p'= Mono_URM_Redpair_Proc projL' trsLL' trsLL2' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f9' projL' trsLL' trsLL2' term')
       (redtriple_impl_assn projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    dp_termination_proof_assn term term' * hn_ctxt XX9 p p' * \<Gamma>9') R (f9 projL trsLL trsLL2 term)"
assumes Mono_Redpair_UR_Proc:
    "\<And>projL trsLL trsLL2 trsLL3 term projL' trsLL' trsLL2' trsLL3' term'.
     \<lbrakk>p=Mono_Redpair_UR_Proc projL trsLL trsLL2 trsLL3 term;
       p'= Mono_Redpair_UR_Proc projL' trsLL' trsLL2' trsLL3' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f10' projL' trsLL' trsLL2' trsLL3' term')
       (id_assn projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    trsLL_assn id_assn id_assn id_assn trsLL3 trsLL3' *
    dp_termination_proof_assn term term' * hn_ctxt XX10 p p' * \<Gamma>10') R (f10 projL trsLL trsLL2 trsLL3 term)"
  assumes Size_Change_Subterm_Proc:
  "\<And>term term'. \<lbrakk>p=Size_Change_Subterm_Proc term;
       p'= Size_Change_Subterm_Proc term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f11' term')
       ( list_assn (rule_assn (lab_assn id_assn id_assn) id_assn *a
       list_assn (nat_assn *a nat_assn) *a list_assn (nat_assn *a nat_assn)) term term' * hn_ctxt XX11 p p' * \<Gamma>11') R (f11 term)"
  assumes Size_Change_Redpair_Proc:
  "\<And>red trsLL term  red' trsLL' term'. \<lbrakk>p=Size_Change_Redpair_Proc  red trsLL term;
       p'= Size_Change_Redpair_Proc  red' trsLL' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f12'  red' trsLL' term')
       (redtriple_impl_assn red red' * option_assn (trsLL_assn id_assn id_assn id_assn) trsLL trsLL' *
    list_assn (rule_assn (lab_assn id_assn id_assn) id_assn *a
       list_assn (nat_assn *a nat_assn) *a list_assn (nat_assn *a nat_assn)) term term' *
        hn_ctxt XX12 p p' * \<Gamma>12') R (f12  red trsLL term)"
  assumes Uncurry_Proc:
  "\<And>n unc trsLL2 trsLL3 term n' unc' trsLL2' trsLL3' term'. \<lbrakk>p=Uncurry_Proc n unc trsLL2 trsLL3 term;
       p'= Uncurry_Proc n' unc' trsLL2' trsLL3' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f13' n' unc' trsLL2' trsLL3' term')
       (option_assn nat_assn n n' *
    id_assn unc unc' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    trsLL_assn id_assn id_assn id_assn trsLL3 trsLL3' *
    dp_termination_proof_assn term term' *
        hn_ctxt XX13 p p' * \<Gamma>13') R (f13 n unc trsLL2 trsLL3 term)"
  assumes Fcc_Proc:
  "\<And>n unc trsLL2 trsLL3 term n' unc' trsLL2' trsLL3' term'. \<lbrakk>p=Fcc_Proc n unc trsLL2 trsLL3 term;
       p'= Fcc_Proc n' unc' trsLL2' trsLL3' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f14' n' unc' trsLL2' trsLL3' term')
       (lab_assn id_assn id_assn n n' *
    id_assn unc unc' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    trsLL_assn id_assn id_assn id_assn trsLL3 trsLL3' *
    dp_termination_proof_assn term term' *
        hn_ctxt XX14 p p' * \<Gamma>14') R (f14 n unc trsLL2 trsLL3 term)"
  assumes Split_Proc:
  "\<And>trsLL trsLL2 term term2 trsLL' trsLL2' term' term2'. \<lbrakk>p=Split_Proc trsLL trsLL2 term term2;
       p'= Split_Proc trsLL' trsLL2' term' term2'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f15' trsLL' trsLL2' term' term2')
       ( trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    dp_termination_proof_assn term term' *
    dp_termination_proof_assn term2 term2' *
        hn_ctxt XX15 p p' * \<Gamma>15') R (f15 trsLL trsLL2 term term2)"
  assumes Semlab_Proc:
  "\<And> sl  trsLL2 unc trsLL3 term  sl' trsLL2' unc' trsLL3' term'. \<lbrakk>p=Semlab_Proc  sl  trsLL2 unc trsLL3 term;
       p'= Semlab_Proc sl' trsLL2' unc' trsLL3' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f16' sl' trsLL2' unc' trsLL3' term')
       (id_assn sl sl' *
    list_assn (term_assn id_assn id_assn) unc unc' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    trsLL_assn id_assn id_assn id_assn trsLL3 trsLL3' *
    dp_termination_proof_assn term term' *
        hn_ctxt XX16 p p' * \<Gamma>16') R (f16  sl  trsLL2 unc trsLL3 term)"
  assumes Switch_Innermost_Proc:
  "\<And> sl term sl' term'. \<lbrakk>p=Switch_Innermost_Proc sl term;
       p'= Switch_Innermost_Proc sl' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f17' sl' term')
       (id_assn sl sl' * dp_termination_proof_assn term term' *
        hn_ctxt XX17 p p' * \<Gamma>17') R (f17 sl term)"
  assumes Rewriting_Proc:
  "\<And> n r1 r2 r3 r4 apos term n' r1' r2' r3' r4' apos' term'. \<lbrakk>p=Rewriting_Proc n r1 r2 r3 r4 apos term;
       p'= Rewriting_Proc n' r1' r2' r3' r4' apos' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f18' n' r1' r2' r3' r4' apos' term')
       (option_assn (trsLL_assn id_assn id_assn id_assn) n n' *
    ruleLL_assn id_assn id_assn id_assn r1 r1' *
    ruleLL_assn id_assn id_assn id_assn r2 r2' *
    ruleLL_assn id_assn id_assn id_assn r3 r3' *
    ruleLL_assn id_assn id_assn id_assn r4 r4' *
    dp_termination_proof_assn term term' *
        hn_ctxt XX18 p p' * \<Gamma>18') R (f18 n r1 r2 r3 r4 apos term)"
 assumes Instantiation_Proc:
  "\<And> r1 trsLL term r1' trsLL' term'. \<lbrakk>p=Instantiation_Proc r1 trsLL term;
       p'= Instantiation_Proc r1' trsLL' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f19' r1' trsLL' term')
       (ruleLL_assn id_assn id_assn id_assn r1 r1' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term' *
        hn_ctxt XX19 p p' * \<Gamma>19') R (f19 r1 trsLL term)"
 assumes Forward_Instantiation_Proc:
  "\<And> r1 trsLL trsLL2 term r1' trsLL' trsLL2' term'. \<lbrakk>p=Forward_Instantiation_Proc r1 trsLL trsLL2 term;
       p'= Forward_Instantiation_Proc r1' trsLL' trsLL2' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f20' r1' trsLL' trsLL2' term')
       (ruleLL_assn id_assn id_assn id_assn r1 r1' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    option_assn (trsLL_assn id_assn id_assn id_assn) trsLL2 trsLL2' *
    dp_termination_proof_assn term term' *
        hn_ctxt XX20 p p' * \<Gamma>20') R (f20 r1 trsLL trsLL2 term)"
  assumes Narrowing_Proc:
  "\<And> r1 apos trsLL term r1' apos' trsLL' term'. \<lbrakk>p=Narrowing_Proc r1 apos trsLL term;
       p'= Narrowing_Proc r1' apos' trsLL' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f21' r1' apos' trsLL' term')
       (ruleLL_assn id_assn id_assn id_assn r1 r1' *
    pos_assn apos apos' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term' *
        hn_ctxt XX21 p p' * \<Gamma>21') R (f21 r1 apos trsLL term)"
  assumes Assume_Finite:
  "\<And> r1 term r1' term'. \<lbrakk>p=Assume_Finite r1 term;
       p'= Assume_Finite r1' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f22' r1' term')
       (id_assn r1 r1' * id_assn term term' *
        hn_ctxt XX22 p p' * \<Gamma>22') R (f22 r1 term)"
 assumes Unlab_Proc:
  "\<And> trsLL trsLL2 term trsLL' trsLL2' term'. \<lbrakk>p=Unlab_Proc trsLL trsLL2 term;
       p'= Unlab_Proc trsLL' trsLL2' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f23' trsLL' trsLL2' term')
       (trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    dp_termination_proof_assn term term' *
        hn_ctxt XX23 p p' * \<Gamma>23') R (f23 trsLL trsLL2 term)"
 assumes Q_Reduction_Proc:
  "\<And> trsLL term trsLL' term'. \<lbrakk>p=Q_Reduction_Proc trsLL term;
       p'= Q_Reduction_Proc trsLL' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f24' trsLL' term')
       (termsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term' *
        hn_ctxt XX24 p p' * \<Gamma>24') R (f24 trsLL term)"
 assumes Complex_Constant_Removal_Proc:
  "\<And> trsLL term trsLL' term'. \<lbrakk>p=Complex_Constant_Removal_Proc trsLL term;
       p'= Complex_Constant_Removal_Proc trsLL' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f25' trsLL' term')
       (id_assn trsLL trsLL' *
    dp_termination_proof_assn term term' *
        hn_ctxt XX25 p p' * \<Gamma>25') R (f25 trsLL term)"
  assumes General_Redpair_Proc:
  "\<And> red trsLL trsLL2 pp term red' trsLL' trsLL2' pp' term'. \<lbrakk>p=General_Redpair_Proc red trsLL trsLL2 pp term;
       p'= General_Redpair_Proc red' trsLL' trsLL2' pp' term'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f26' red' trsLL' trsLL2' pp' term')
       (redtriple_impl_assn red red' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    id_assn pp pp' *
    list_assn dp_termination_proof_assn term term' *
        hn_ctxt XX26 p p' * \<Gamma>26') R (f26 red trsLL trsLL2 pp term)"
  assumes To_Trs_Proc:
  "\<And> red red'. \<lbrakk>p=To_Trs_Proc red;
       p'= To_Trs_Proc red'\<rbrakk> \<Longrightarrow>
    hn_refine (INVE * F) (f27' red')
       (trs_termination_proof_assn red red' *
        hn_ctxt XX27 p p' * \<Gamma>27') R (f27 red)"
  assumes MERGE1: "\<Gamma>1' \<or>\<^sub>A \<Gamma>2' \<or>\<^sub>A \<Gamma>3' \<or>\<^sub>A \<Gamma>4'  \<or>\<^sub>A \<Gamma>5' \<or>\<^sub>A \<Gamma>6' \<or>\<^sub>A \<Gamma>7' \<or>\<^sub>A \<Gamma>8' \<or>\<^sub>A \<Gamma>9' \<or>\<^sub>A \<Gamma>10' \<or>\<^sub>A
         \<Gamma>11' \<or>\<^sub>A \<Gamma>12' \<or>\<^sub>A \<Gamma>13' \<or>\<^sub>A \<Gamma>14' \<or>\<^sub>A \<Gamma>15' \<or>\<^sub>A \<Gamma>16' \<or>\<^sub>A
         \<Gamma>17' \<or>\<^sub>A \<Gamma>18' \<or>\<^sub>A \<Gamma>19' \<or>\<^sub>A \<Gamma>20' \<or>\<^sub>A \<Gamma>21' \<or>\<^sub>A \<Gamma>22' \<or>\<^sub>A \<Gamma>23' \<or>\<^sub>A \<Gamma>24'  \<or>\<^sub>A \<Gamma>25' \<or>\<^sub>A \<Gamma>26' \<or>\<^sub>A \<Gamma>27' \<Longrightarrow>\<^sub>t \<Gamma>'"
  shows
    "hn_refine \<Gamma>
      (case_dp_termination_proof f1' f2' f3' f4' f5' f6' f7' f8' f9' f10' f11' f12' f13' f14' f15'
       f16' f17' f18' f19' f20' f21' f22' f23' f24' f25' f26' f27' p')
      (hn_ctxt (dp_termination_proof_assn) p p' * \<Gamma>') R
      (case_dp_termination_proof$f1$ABS5 f2$ABS4 f3$ABS4 f4$ABS5 f5$ABS3 f6$ABS2 f7
  $ABS2 f8$ABS5 f9$ABS5 f10$ABS2 f11$ABS4 f12$ABS6 f13$ABS6 f14$ABS5 f15$ABS6 f16$ABS3 f17
  $ABS8 f18$ABS4 f19$ABS5 f20$ABS5 f21$ABS3 f22$ABS4 f23$ABS3 f24$ABS3 f25$ABS6 f26$ABS2 f27$p)"
  supply [[goals_limit=1]]
  apply (rule hn_refine_cons_pre[OF FR])
  apply1 extract_hnr_invalids
  apply (subst dp_termination_proof_assn.simps[THEN hn_dp_termination_proof_assn])
  apply (cases p; cases p';
    simp only: PROTECT2_def APP_def dp_termination_proof.case prod.case
     star_false_left hn_refine_false)
  subgoal
    apply (rule hn_refine_cons[OF _ P_is_Empty _ entt_refl]; assumption?)
     applyS (simp add: hn_ctxt_def dp_termination_proof_assn.simps)
    apply (simp add: hn_ctxt_def dp_termination_proof_assn.simps)
    apply1 (rule entt_trans[OF _ MERGE1])
    applyS (simp add: entt_disjI1' entt_disjI2' entt_fr_drop')
    done
  subgoal by (hn_case_proof ccase:Subterm_Criterion_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Gen_Subterm_Criterion_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Redpair_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Redpair_UR_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Usable_Rules_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Dep_Graph_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Mono_Redpair_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Mono_URM_Redpair_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase: Mono_Redpair_UR_Proc merge: MERGE1)
  subgoal by (hn_case_proof ccase:Size_Change_Subterm_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Size_Change_Redpair_Proc merge:MERGE1)
  subgoal by (hn_case_proof_internal ccase:Uncurry_Proc merge:MERGE1)
  subgoal by (hn_case_proof_internal ccase:Fcc_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Split_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Semlab_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Switch_Innermost_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Rewriting_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Instantiation_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Forward_Instantiation_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Narrowing_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Assume_Finite merge:MERGE1)
  subgoal by (hn_case_proof ccase:Unlab_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Q_Reduction_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:Complex_Constant_Removal_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:General_Redpair_Proc merge:MERGE1)
  subgoal by (hn_case_proof ccase:To_Trs_Proc merge:MERGE1)
  done

end