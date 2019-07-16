theory WB_More_IICF_LLVM
imports 
  Isabelle_LLVM.IICF 
  Isabelle_LLVM.Sepref_HOL_Bindings 
  WB_More_Refinement
begin

paragraph \<open>This is not part of the multiset setup\<close>

(*
definition "list_mset_assn A \<equiv> pure (list_mset_rel O \<langle>the_pure A\<rangle>mset_rel)"
declare list_mset_assn_def[symmetric,fcomp_norm_unfold]
lemma [safe_constraint_rules]: "is_pure (list_mset_assn A)" unfolding list_mset_assn_def by simp
*)

no_notation prod_assn (infixr "\<times>\<^sub>a" 70)
notation prod_assn (infixr "*a" 70)

lemma prod_assn_id_assn_destroy:
  fixes R :: \<open>_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> bool\<close>
  shows \<open>R\<^sup>d *\<^sub>a id_assn\<^sup>d = (R *a id_assn)\<^sup>d\<close>
  apply (auto simp: hfprod_def prod_assn_def[abs_def] invalid_assn_def pure_def intro!: ext)
  apply (metis (full_types) pred_lift_extract_simps(2) pure_true_conv sep.add.right_neutral)
  by (metis Sep_Algebra_Add.pure_part_pure pred_lift_extract_simps(1) pred_lift_extract_simps(2)
    pure_part_split_conj)


(*lemma
 shows list_mset_assn_add_mset_Nil:
     \<open>list_mset_assn R (add_mset q Q) [] = (\<lambda>_. False)\<close> and
   list_mset_assn_empty_Cons:
    \<open>list_mset_assn R {#} (x # xs) = (\<lambda>_. False)\<close> and
   list_mset_assn_empty_nil:
    \<open>list_mset_assn R {#} [] = \<box>\<close>
  unfolding list_mset_assn_def list_mset_rel_def mset_rel_def pure_def p2rel_def
    rel2p_def rel_mset_def br_def
  by (sep_auto simp: Collect_eq_comp pure_true_conv)+
*)

lemma Exists_eq_simp: \<open>(\<exists>x. (P x \<and>* \<up> (x = b)) s) \<longleftrightarrow> P b s\<close>
  apply (auto)
  apply (metis (full_types) Sep_Algebra_Add.pure_part_pure pure_partI pure_part_split_conj pure_true_conv sep.add.right_neutral)
  by (metis (full_types)pure_true_conv sep_conj_sep_emptyE)

lemma \<open>(\<up>(x = b)) s \<longleftrightarrow> x = b \<and> \<box> s\<close>
  by (auto simp: pred_lift_def)
lemma split_conj_is_pure:
  assumes \<open>Sepref_Basic.is_pure B\<close>
  shows \<open>(B b bi \<and>* R) s = ((bi, b) \<in> the_pure B \<and> R s)\<close> (is ?A)
proof -
  obtain B' where R: \<open>B = pure B'\<close> using assms unfolding is_pure_conv ..
  then have R': \<open>B' = the_pure B\<close> by simp
  show A: ?A
    unfolding R'[symmetric] unfolding R pure_def pred_lift_extract_simps
    by auto
qed
lemma split_conj_is_pure2:
  assumes \<open>Sepref_Basic.is_pure B\<close>
  shows
      \<open>(R1 \<and>* B b bi \<and>* R) s = ((bi, b) \<in> the_pure B \<and> (R1 \<and>* R) s)\<close> (is ?B)
  apply (subst sep_algebra_class.sep_conj_left_commute)
  apply (subst split_conj_is_pure[OF assms])
  apply simp
  done

(*
lemma snd_hnr_pure:
   \<open>CONSTRAINT is_pure B \<Longrightarrow> (return \<circ> snd, RETURN \<circ> snd) \<in> A\<^sup>d *\<^sub>a B\<^sup>k \<rightarrow>\<^sub>a B\<close>
  apply sepref_to_hoare
  apply (sep_auto simp: htriple_def wp_def mwp_def Monad.return_def pure_true_conv split_conj_is_pure
    split_conj_is_pure2 pred_lift_def)
  oops
*)

(*
lemma list_mset_assn_pure_conv:
  \<open>list_mset_assn (pure R) = pure (\<langle>R\<rangle>list_rel_mset_rel)\<close>
proof -
  have [iff]: \<open>(\<forall>x x'. ((x', x) \<in> R) = ((x', x) \<in> P')) \<longleftrightarrow> R = P'\<close> for P'
    by auto
  have [simp]: \<open>the_pure (\<lambda>a c. \<up>((c, a) \<in> R)) = R\<close>
    by (auto simp: the_pure_def)

  show ?thesis
    apply (intro ext)
    using list_all2_reorder_left_invariance[of \<open>(\<lambda>x x'. (x, x') \<in> R)\<close>]
    by (fastforce
      simp: list_rel_mset_rel_def list_mset_assn_def
      mset_rel_def rel2p_def[abs_def] rel_mset_def p2rel_def
      list_mset_rel_def[abs_def] Collect_eq_comp br_def pred_lift_def
      list_rel_def Collect_eq_comp_right Sepref_Basic.pure_def
    intro!: arg_cong[of _ _ \<open>\<lambda>b. pure b _ _\<close>])
qed
*)


lemma nempty_list_mset_rel_iff: \<open>M \<noteq> {#} \<Longrightarrow>
  (xs, M) \<in> list_mset_rel \<longleftrightarrow> (xs \<noteq> [] \<and> hd xs \<in># M \<and>
         (tl xs, remove1_mset (hd xs) M) \<in> list_mset_rel)\<close>
  by (cases xs) (auto simp: list_mset_rel_def br_def dest!: multi_member_split)

(*abbreviation ghost_assn where
  \<open>ghost_assn \<equiv> hr_comp unit_assn virtual_copy_rel\<close>
*)  

text \<open>This function does not change the size of the underlying array.\<close>
definition take1 where
  \<open>take1 xs = take 1 xs\<close>


text \<open>The following two abbreviation are variants from \<^term>\<open>uncurry4\<close> and
   \<^term>\<open>uncurry6\<close>. The problem is that \<^term>\<open>uncurry2 (uncurry2 f)\<close> and
   \<^term>\<open>uncurry (uncurry3 f)\<close> are the same term, but only the latter is folded
   to \<^term>\<open>uncurry4\<close>.\<close>
abbreviation uncurry4' where
  "uncurry4' f \<equiv> uncurry2 (uncurry2 f)"

abbreviation uncurry6' where
  "uncurry6' f \<equiv> uncurry2 (uncurry4' f)"


lemma hrp_comp_Id2[simp]: \<open>hrp_comp A Id = A\<close>
  unfolding hrp_comp_def by auto

(*
lemma norm_RETURN_o[to_hnr_post]:
  "\<And>f. (RETURN oooo f)$x$y$z$a = (RETURN$(f$x$y$z$a))"
  "\<And>f. (RETURN ooooo f)$x$y$z$a$b = (RETURN$(f$x$y$z$a$b))"
  "\<And>f. (RETURN oooooo f)$x$y$z$a$b$c = (RETURN$(f$x$y$z$a$b$c))"
  "\<And>f. (RETURN ooooooo f)$x$y$z$a$b$c$d = (RETURN$(f$x$y$z$a$b$c$d))"
  "\<And>f. (RETURN oooooooo f)$x$y$z$a$b$c$d$e = (RETURN$(f$x$y$z$a$b$c$d$e))"
  "\<And>f. (RETURN ooooooooo f)$x$y$z$a$b$c$d$e$g = (RETURN$(f$x$y$z$a$b$c$d$e$g))"
  "\<And>f. (RETURN oooooooooo f)$x$y$z$a$b$c$d$e$g$h= (RETURN$(f$x$y$z$a$b$c$d$e$g$h))"
  "\<And>f. (RETURN \<circ>\<^sub>1\<^sub>1 f)$x$y$z$a$b$c$d$e$g$h$i= (RETURN$(f$x$y$z$a$b$c$d$e$g$h$i))"
  "\<And>f. (RETURN \<circ>\<^sub>1\<^sub>2 f)$x$y$z$a$b$c$d$e$g$h$i$j= (RETURN$(f$x$y$z$a$b$c$d$e$g$h$i$j))"
  "\<And>f. (RETURN \<circ>\<^sub>1\<^sub>3 f)$x$y$z$a$b$c$d$e$g$h$i$j$l= (RETURN$(f$x$y$z$a$b$c$d$e$g$h$i$j$l))"
  "\<And>f. (RETURN \<circ>\<^sub>1\<^sub>4 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m= (RETURN$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m))"
  "\<And>f. (RETURN \<circ>\<^sub>1\<^sub>5 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n= (RETURN$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n))"
  "\<And>f. (RETURN \<circ>\<^sub>1\<^sub>6 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p= (RETURN$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p))"
  "\<And>f. (RETURN \<circ>\<^sub>1\<^sub>7 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r=
    (RETURN$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r))"
  "\<And>f. (RETURN \<circ>\<^sub>1\<^sub>8 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s=
    (RETURN$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s))"
  "\<And>f. (RETURN \<circ>\<^sub>1\<^sub>9 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s$t=
    (RETURN$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s$t))"
  "\<And>f. (RETURN \<circ>\<^sub>2\<^sub>0 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s$t$u=
    (RETURN$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s$t$u))"
  by auto

lemma norm_return_o[to_hnr_post]:
  "\<And>f. (return oooo f)$x$y$z$a = (return$(f$x$y$z$a))"
  "\<And>f. (return ooooo f)$x$y$z$a$b = (return$(f$x$y$z$a$b))"
  "\<And>f. (return oooooo f)$x$y$z$a$b$c = (return$(f$x$y$z$a$b$c))"
  "\<And>f. (return ooooooo f)$x$y$z$a$b$c$d = (return$(f$x$y$z$a$b$c$d))"
  "\<And>f. (return oooooooo f)$x$y$z$a$b$c$d$e = (return$(f$x$y$z$a$b$c$d$e))"
  "\<And>f. (return ooooooooo f)$x$y$z$a$b$c$d$e$g = (return$(f$x$y$z$a$b$c$d$e$g))"
  "\<And>f. (return oooooooooo f)$x$y$z$a$b$c$d$e$g$h= (return$(f$x$y$z$a$b$c$d$e$g$h))"
  "\<And>f. (return \<circ>\<^sub>1\<^sub>1 f)$x$y$z$a$b$c$d$e$g$h$i= (return$(f$x$y$z$a$b$c$d$e$g$h$i))"
  "\<And>f. (return \<circ>\<^sub>1\<^sub>2 f)$x$y$z$a$b$c$d$e$g$h$i$j= (return$(f$x$y$z$a$b$c$d$e$g$h$i$j))"
  "\<And>f. (return \<circ>\<^sub>1\<^sub>3 f)$x$y$z$a$b$c$d$e$g$h$i$j$l= (return$(f$x$y$z$a$b$c$d$e$g$h$i$j$l))"
  "\<And>f. (return \<circ>\<^sub>1\<^sub>4 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m= (return$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m))"
  "\<And>f. (return \<circ>\<^sub>1\<^sub>5 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n= (return$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n))"
  "\<And>f. (return \<circ>\<^sub>1\<^sub>6 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p= (return$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p))"
  "\<And>f. (return \<circ>\<^sub>1\<^sub>7 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r=
    (return$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r))"
  "\<And>f. (return \<circ>\<^sub>1\<^sub>8 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s=
    (return$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s))"
  "\<And>f. (return \<circ>\<^sub>1\<^sub>9 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s$t=
    (return$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s$t))"
  "\<And>f. (return \<circ>\<^sub>2\<^sub>0 f)$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s$t$u=
    (return$(f$x$y$z$a$b$c$d$e$g$h$i$j$l$m$n$p$r$s$t$u))"
    by auto
*)

lemma nfoldli_cong2:
  assumes
    le: \<open>length l = length l'\<close> and
    \<sigma>: \<open>\<sigma> = \<sigma>'\<close> and
    c: \<open>c = c'\<close> and
    H: \<open>\<And>\<sigma> x. x < length l \<Longrightarrow> c' \<sigma> \<Longrightarrow> f (l ! x) \<sigma> = f' (l' ! x) \<sigma>\<close>
  shows \<open>nfoldli l c f \<sigma> = nfoldli l' c' f' \<sigma>'\<close>
proof -
  show ?thesis
    using le H unfolding c[symmetric] \<sigma>[symmetric]
  proof (induction l arbitrary: l' \<sigma>)
    case Nil
    then show ?case by simp
  next
    case (Cons a l l'') note IH=this(1) and le = this(2) and H = this(3)
    show ?case
      using le H[of \<open>Suc _\<close>] H[of 0] IH[of \<open>tl l''\<close> \<open>_\<close>]
      by (cases l'')
        (auto intro: bind_cong_nres)
  qed
qed

(*This is rather different from the SML version*)
lemma list_rel_update:
  assumes rel: \<open>(xs, ys) \<in> \<langle>the_pure R\<rangle>list_rel\<close> and
   h: \<open>R b bi s\<close> and
   p: \<open>is_pure R\<close>
  shows \<open>(list_update xs ba bi, list_update ys ba b) \<in> \<langle>the_pure R\<rangle>list_rel\<close>
proof -
  obtain R' where R: \<open>the_pure R = R'\<close> and R': \<open>R = pure R'\<close>
    using p by fastforce
  have [simp]: \<open>(bi, b) \<in> the_pure R\<close>
    using h p by (auto simp: R R' pure_app_eq pred_lift_extract_simps)
  have \<open>length xs = length ys\<close>
    using assms list_rel_imp_same_length by blast

  then show ?thesis
    using rel
    by (induction xs ys arbitrary: ba rule: list_induct2) (auto split: nat.splits)
qed



(*TODO: Move + Kill*)

definition [simp]: "arl_array_replicate_init i n \<equiv> replicate n i"
interpretation arl: replicate_init arl_array_replicate_init by unfold_locales simp

context
  fixes l_dummy :: "'l::len2 itself" 
    and L AA
  defines [simp]: "L \<equiv> (LENGTH ('l))"
  defines [simp]: "AA \<equiv> raw_al_assn :: _ \<Rightarrow> (_,'l) array_list \<Rightarrow> _" 
begin

private lemma n_unf: "hr_comp AA (\<langle>the_pure A\<rangle>list_rel) = al_assn A" unfolding al_assn_def AA_def ..

context
  notes [fcomp_norm_unfold] = n_unf
  notes [simp] = refine_pw_simps
begin


sepref_decl_op arl_custom_replicate: op_list_replicate :: "nat_rel \<rightarrow> A \<rightarrow> \<langle>A\<rangle>list_rel" .

definition arl_aux_replicate where
  \<open>arl_aux_replicate ai bi = doM {
         x \<leftarrow> narray_new_init ai bi;
         return (ai, ai, x)
       }\<close>

lemma arl_aux_replicate_rule[vcg_rules]: 
  "llvm_htriple 
    (\<upharpoonleft>snat.assn c (ci :: 'b :: len2 word) ** \<up>(4 < LENGTH('b)))
    (arl_aux_replicate ci b)
    (\<lambda>ri. \<upharpoonleft>snat.assn c ci ** raw_al_assn (replicate c b) ri)"
proof -
  (*why?*)
  have H: \<open>(\<up>(Q) \<and>* (\<lambda>a. \<exists>x xa xb. (P x xa xb) a) \<and>* F) =
    (\<lambda>a. \<exists>x xa xb. (\<up>(Q) \<and>* P x xa xb \<and>* F) a)\<close> for P F Q
  apply (auto simp: ENTAILS_def arl_assn_def arl_assn'_def pure_true_conv
      snat.assn_is_rel pure_app_eq snat.rel_def br_def 
      pred_lift_extract_simps intro!: ext
      )
    apply (smt sep_conjD sep_conjI)
    by (smt sep_conj_impl)
  have H': \<open> \<flat>\<^sub>psnat.assn c ci \<longleftrightarrow> (ci, c) \<in> snat.rel\<close>
    by (simp add: dr_assn_pure_asm_prefix_def snat.assn_is_rel snat.assn_pure)
  show ?thesis
    unfolding arl_aux_replicate_def
    apply (vcg_monadify)
    apply vcg'
    apply (auto simp: ENTAILS_def arl_assn_def arl_assn'_def pure_true_conv
        snat.assn_is_rel pure_app_eq
        simp flip: pred_lift_extract_simps extract_pure_assn
        )
    apply (subst H)
    apply (rule_tac x=c in entails_exI)
    apply (rule_tac x=c in entails_exI)
    apply (rule_tac x= \<open>replicate c b\<close> in entails_exI)
    apply (auto simp: H' pure_true_conv)
    apply (rule Defer_Slot.remove_slot)
    done
qed

  lemma hn_arl_repl_init_raw:
    shows "(\<lambda>xi. arl_aux_replicate (xi :: 'l ::len2 word) init,RETURN o replicate_init_raw) \<in>
      [\<lambda>_. 4 < L]\<^sub>a snat_assn\<^sup>k \<rightarrow> AA"
    unfolding snat_rel_def snat.assn_is_rel[symmetric]
    apply sepref_to_hoare
    apply vcg'
    done

  sepref_decl_impl (no_mop) hn_arl_repl_init_raw uses arl.replicate_init_param
    by auto

  lemma hn_arl_replicate_new_raw:
   "(uncurry (arl_aux_replicate :: 'l word \<Rightarrow> _), uncurry (RETURN oo op_arl_custom_replicate)) \<in> [\<lambda>_. L > 4]\<^sub>a snat_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow> AA"
    unfolding snat_rel_def snat.assn_is_rel[symmetric]
    apply sepref_to_hoare
    by vcg'
    
  sepref_decl_impl hn_arl_replicate_new_raw by auto

end
end

lemma arl_fold_custom_replicate: 
  "replicate = op_arl_custom_replicate"
  "op_list_replicate = op_arl_custom_replicate"
  "mop_list_replicate = mop_arl_custom_replicate"
  by (auto del: ext intro!: ext)
end
