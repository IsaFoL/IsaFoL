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

fun dp_termination_proof_assn  ::
    "('e, 'f, 'g) dp_termination_proof \<Rightarrow> ('e, 'f, 'g) dp_termination_proof \<Rightarrow> assn" and
   trs_termination_proof_assn ::
    "('e, 'f, 'g) trs_termination_proof \<Rightarrow> ('e, 'f, 'g) trs_termination_proof \<Rightarrow> assn"
where
 \<open>dp_termination_proof_assn P_is_Empty P_is_Empty = emp\<close> |
 \<open>dp_termination_proof_assn
      (Subterm_Criterion_Proc projL rseqL trsLL term)
      (Subterm_Criterion_Proc projL' rseqL' trsLL' term') =
    projL_assn (lab_assn id_assn id_assn) projL projL' *
    rseqL_assn id_assn id_assn id_assn  rseqL rseqL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term'\<close> |
 \<open>dp_termination_proof_assn
      (Gen_Subterm_Criterion_Proc projL trsLL term)
      (Gen_Subterm_Criterion_Proc projL' trsLL' term') =
    status_impl_assn (lab_assn id_assn id_assn) projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term'\<close> |
 \<open>dp_termination_proof_assn
      (Redpair_Proc projL trsLL term)
      (Redpair_Proc projL' trsLL' term') =
    (root_redtriple_impl_assn +\<^sub>a redtriple_impl_assn) projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term'\<close> |
 \<open>dp_termination_proof_assn
      (Redpair_UR_Proc projL trsLL trsLL2 term)
      (Redpair_UR_Proc projL' trsLL' trsLL2' term') =
    (root_redtriple_impl_assn +\<^sub>a redtriple_impl_assn) projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    dp_termination_proof_assn term term'\<close> |
 \<open>dp_termination_proof_assn
      (Usable_Rules_Proc trsLL term)
      (Usable_Rules_Proc trsLL' term') =
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term'\<close> |
 \<open>dp_termination_proof_assn
      (Dep_Graph_Proc term)
      (Dep_Graph_Proc term') =
    list_assn (option_assn dp_termination_proof_assn *a
      trsLL_assn id_assn id_assn id_assn) term term'\<close> |
 \<open>dp_termination_proof_assn
      (Mono_Redpair_Proc projL trsLL trsLL2 term)
      (Mono_Redpair_Proc projL' trsLL' trsLL2' term') =
    redtriple_impl_assn projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    dp_termination_proof_assn term term'\<close> |
 \<open>dp_termination_proof_assn
      (Mono_URM_Redpair_Proc projL trsLL trsLL2 term)
      (Mono_URM_Redpair_Proc projL' trsLL' trsLL2' term') =
    redtriple_impl_assn projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    dp_termination_proof_assn term term'\<close> |
 \<open>dp_termination_proof_assn
      (Mono_Redpair_UR_Proc projL trsLL trsLL2 trsLL3 term)
      (Mono_Redpair_UR_Proc projL' trsLL' trsLL2' trsLL3' term') =
    id_assn projL projL' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    trsLL_assn id_assn id_assn id_assn trsLL3 trsLL3' *
    dp_termination_proof_assn term term'\<close> |
 \<open>dp_termination_proof_assn
      (Size_Change_Subterm_Proc term)
      (Size_Change_Subterm_Proc term') =
    list_assn (rule_assn (lab_assn id_assn id_assn) id_assn *a
       list_assn (nat_assn *a nat_assn) *a list_assn (nat_assn *a nat_assn)) term term'\<close> |
 \<open>dp_termination_proof_assn
      (Size_Change_Redpair_Proc red trsLL term)
      (Size_Change_Redpair_Proc red' trsLL' term') =
    redtriple_impl_assn red red' * option_assn (trsLL_assn id_assn id_assn id_assn) trsLL trsLL' *
    list_assn (rule_assn (lab_assn id_assn id_assn) id_assn *a
       list_assn (nat_assn *a nat_assn) *a list_assn (nat_assn *a nat_assn)) term term'\<close> |
 \<open>dp_termination_proof_assn
      (Uncurry_Proc n unc trsLL2 trsLL3 term)
      (Uncurry_Proc n' unc' trsLL2' trsLL3' term') =
    option_assn nat_assn n n' *
    id_assn unc unc' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    trsLL_assn id_assn id_assn id_assn trsLL3 trsLL3' *
    dp_termination_proof_assn term term'\<close> |
 \<open>dp_termination_proof_assn
      (Fcc_Proc n unc trsLL2 trsLL3 term)
      (Fcc_Proc n' unc' trsLL2' trsLL3' term') =
    lab_assn id_assn id_assn n n' *
    id_assn unc unc' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    trsLL_assn id_assn id_assn id_assn trsLL3 trsLL3' *
    dp_termination_proof_assn term term'\<close> |
 \<open>dp_termination_proof_assn
      (Split_Proc trsLL trsLL2 term term2)
      (Split_Proc trsLL' trsLL2' term' term2') =
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    dp_termination_proof_assn term term' *
    dp_termination_proof_assn term2 term2'\<close> |
 \<open>dp_termination_proof_assn
      (Semlab_Proc sl  trsLL2 unc trsLL3 term)
      (Semlab_Proc sl' trsLL2' unc' trsLL3' term') =
    id_assn sl sl' *
    list_assn (term_assn id_assn id_assn) unc unc' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    trsLL_assn id_assn id_assn id_assn trsLL3 trsLL3' *
    dp_termination_proof_assn term term'\<close> |
 \<open>dp_termination_proof_assn
      (Switch_Innermost_Proc sl term)
      (Switch_Innermost_Proc sl' term') =
    id_assn sl sl' *
    dp_termination_proof_assn term term'\<close> |
 \<open>dp_termination_proof_assn
      (Rewriting_Proc n r1 r2 r3 r4 apos term)
      (Rewriting_Proc n' r1' r2' r3' r4' apos' term') =
    option_assn (trsLL_assn id_assn id_assn id_assn) n n' *
    ruleLL_assn id_assn id_assn id_assn r1 r1' *
    ruleLL_assn id_assn id_assn id_assn r2 r2' *
    ruleLL_assn id_assn id_assn id_assn r3 r3' *
    ruleLL_assn id_assn id_assn id_assn r4 r4' *
    dp_termination_proof_assn term term'\<close> |
 \<open>dp_termination_proof_assn
      (Instantiation_Proc r1 trsLL term)
      (Instantiation_Proc r1' trsLL' term') =
    ruleLL_assn id_assn id_assn id_assn r1 r1' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term'\<close> |
 \<open>dp_termination_proof_assn
      (Forward_Instantiation_Proc r1 trsLL trsLL2 term)
      (Forward_Instantiation_Proc r1' trsLL' trsLL2' term') =
    ruleLL_assn id_assn id_assn id_assn r1 r1' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    option_assn (trsLL_assn id_assn id_assn id_assn) trsLL2 trsLL2' *
    dp_termination_proof_assn term term'\<close> |
 \<open>dp_termination_proof_assn
      (Narrowing_Proc r1 apos trsLL term)
      (Narrowing_Proc r1' apos' trsLL' term') =
    ruleLL_assn id_assn id_assn id_assn r1 r1' *
    pos_assn apos apos' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term'\<close> |
 \<open>dp_termination_proof_assn
      (Assume_Finite r1 term)
      (Assume_Finite r1' term') =
    id_assn r1 r1' *
    id_assn term term'\<close> | (* cheating *)
 \<open>dp_termination_proof_assn
      (Unlab_Proc trsLL trsLL2 term)
      (Unlab_Proc trsLL' trsLL2' term') =
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    dp_termination_proof_assn term term'\<close> |
 \<open>dp_termination_proof_assn
      (Q_Reduction_Proc trsLL term)
      (Q_Reduction_Proc trsLL' term') =
    termsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    dp_termination_proof_assn term term'\<close> |
 \<open>dp_termination_proof_assn
      (Complex_Constant_Removal_Proc trsLL term)
      (Complex_Constant_Removal_Proc trsLL' term') =
    id_assn trsLL trsLL' *
    dp_termination_proof_assn term term'\<close> |
 \<open>dp_termination_proof_assn
      (General_Redpair_Proc red trsLL trsLL2 p term)
      (General_Redpair_Proc red' trsLL' trsLL2' p' term') =
    redtriple_impl_assn red red' * 
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    id_assn p p' *
    list_assn dp_termination_proof_assn term term'\<close> |
 \<open>dp_termination_proof_assn
      (To_Trs_Proc red)
      (To_Trs_Proc red') =
    trs_termination_proof_assn red red'\<close> |

\<open>trs_termination_proof_assn
     (DP_Trans b1 b2 r dp)
     (DP_Trans b1' b2' r' dp') =
   bool_assn b1 b1' * bool_assn b2 b2' *
   rules_assn id_assn id_assn r r' *
   dp_termination_proof_assn dp dp'\<close> |
\<open>trs_termination_proof_assn
     (Rule_Removal r trsLL ts)
     (Rule_Removal r' trsLL' ts') =
   redtriple_impl_assn r r' *
   trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
   trs_termination_proof_assn ts ts'\<close> |
\<open>trs_termination_proof_assn
     (String_Reversal ts)
     (String_Reversal ts') =
   trs_termination_proof_assn ts ts'\<close> |
\<open>trs_termination_proof_assn
     (Constant_String a ts)
     (Constant_String a' ts') =
   id_assn a a' *
   trs_termination_proof_assn ts ts'\<close> |
\<open>trs_termination_proof_assn
     (Bounds a)
     (Bounds a') =
   id_assn a a'\<close> |
\<open>trs_termination_proof_assn
      (Uncurry unc trsLL2  ts)
      (Uncurry unc' trsLL2' ts') =
    id_assn unc unc' *
    trsLL_assn id_assn id_assn id_assn trsLL2 trsLL2' *
    trs_termination_proof_assn ts ts'\<close> |
 \<open>trs_termination_proof_assn
      (Semlab sl term trsLL ts)
      (Semlab sl' term' trsLL' ts') =
    id_assn sl sl' *
    list_assn (term_assn id_assn id_assn) term term' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trs_termination_proof_assn ts ts'\<close> |
 \<open>trs_termination_proof_assn R_is_Empty R_is_Empty = true\<close> |
 \<open>trs_termination_proof_assn
      (Fcc sl trsLL ts)
      (Fcc sl' trsLL' ts') =
    id_assn sl sl' *
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trs_termination_proof_assn ts ts'\<close> |
 \<open>trs_termination_proof_assn
      (Split trsLL ts1 ts2)
      (Split trsLL' ts1' ts2') =
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trs_termination_proof_assn ts1 ts1' *
    trs_termination_proof_assn ts2 ts2'\<close> |
 \<open>trs_termination_proof_assn
      (Switch_Innermost sl ts)
      (Switch_Innermost sl' ts') =
    id_assn sl sl' *
    trs_termination_proof_assn ts ts'\<close>  |
 \<open>trs_termination_proof_assn
      (Drop_Equality ts)
      (Drop_Equality ts') =
    trs_termination_proof_assn ts ts'\<close> |
 \<open>trs_termination_proof_assn
      (Remove_Nonapplicable_Rules trsLL ts1)
      (Remove_Nonapplicable_Rules trsLL' ts1') =
    trsLL_assn id_assn id_assn id_assn trsLL trsLL' *
    trs_termination_proof_assn ts1 ts1'\<close> |
 \<open>trs_termination_proof_assn
      (Permuting_AFS trsLL ts1)
      (Permuting_AFS trsLL' ts1') =
    id_assn trsLL trsLL' *
    trs_termination_proof_assn ts1 ts1'\<close> |
 \<open>trs_termination_proof_assn
      (Assume_SN trsLL ts1)
      (Assume_SN trsLL' ts1') =
    id_assn trsLL trsLL' *
    id_assn ts1 ts1'\<close> |
 \<open>dp_termination_proof_assn _ _ = false\<close> | 
 \<open>trs_termination_proof_assn _ _ = false\<close>

end