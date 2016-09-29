theory DRAT_Misc
imports IICF
begin

  (* TODO: Move to Misc *)  
  lemma same_fst_trancl[simp]: "(same_fst P R)\<^sup>+ = same_fst P (\<lambda>x. (R x)\<^sup>+)"
  proof -
    {
      fix x y
      assume "(x,y)\<in>(same_fst P R)\<^sup>+"
      hence "(x,y)\<in>same_fst P (\<lambda>x. (R x)\<^sup>+)"
        by induction (auto simp: same_fst_def)
    } moreover {
      fix f f' x y
      assume "((f,x),(f',y))\<in>same_fst P (\<lambda>x. (R x)\<^sup>+)"
      hence [simp]: "f'=f" "P f" and 1: "(x,y)\<in>(R f)\<^sup>+" by (auto simp: same_fst_def)
      from 1 have "((f,x),(f',y))\<in>(same_fst P R)\<^sup>+"
        apply induction
        subgoal by (rule r_into_trancl) auto
        subgoal by (erule trancl_into_trancl) auto
        done
    } ultimately show ?thesis by auto
  qed  


  (* TODO: Move to Misc *)  
  lemma nth_append_first[simp]: "i<length l \<Longrightarrow> (l@l')!i = l!i"
    by (simp add: nth_append) 


  (* TODO: Move, close to RETURN_SPEC_refine *)
  lemma RETURN_RES_refine:
    assumes "\<exists>x'. (x,x')\<in>R \<and> x'\<in>X"
    shows "RETURN x \<le> \<Down>R (RES X)"
    using assms 
    by (auto simp: pw_le_iff refine_pw_simps)
  
  (* TODO: Move: Refine_Basic/convenience*)  
  lemma refine_IdI: "m \<le> m' \<Longrightarrow> m \<le> \<Down>Id m'" by simp

  (* TODO: Move, check DUP *)
  lemma map_leI[intro?]: "\<lbrakk>\<And>x v. m1 x = Some v \<Longrightarrow> m2 x = Some v\<rbrakk> \<Longrightarrow> m1\<subseteq>\<^sub>mm2"
    unfolding map_le_def by force
  lemma map_leD: "m1\<subseteq>\<^sub>mm2 \<Longrightarrow> m1 k = Some v \<Longrightarrow> m2 k = Some v"
    unfolding map_le_def by force

  (* TODO: Move *)
  lemma card_doubleton_eq_2_iff[simp]: "card {a,b} = 2 \<longleftrightarrow> a\<noteq>b" by auto

  lemma in_set_image_conv_nth: "f x \<in> f`set l \<longleftrightarrow> (\<exists>i<length l. f (l!i) = f x)"
    by (auto simp: in_set_conv_nth) (metis image_eqI nth_mem)

  lemma set_image_eq_pointwiseI: 
    assumes "length l = length l'"
    assumes "\<And>i. i<length l \<Longrightarrow> f (l!i) = f (l'!i)"  
    shows "f`set l = f`set l'"
    using assms
    by (fastforce simp: in_set_conv_nth in_set_image_conv_nth)
    
  lemma insert_swap_set_eq: "i<length l \<Longrightarrow> insert (l!i) (set (l[i:=x])) = insert x (set l)"
    by (auto simp: in_set_conv_nth nth_list_update split: split_if_asm)


  (* TODO: Move *)  
  text \<open>Allows refine-rules to add \<open>RELATES\<close> goals if they introduce hidden relations\<close>
  lemma RELATES_pattern[refine_dref_pattern]: "RELATES R \<Longrightarrow> RELATES R" .
  lemmas [refine_hsimp] = RELATES_def 

  (* TODO: Move. And join with SELECT, and whatever we have there! *)  
  definition "OBTAIN P \<equiv> ASSERT (\<exists>x. P x) \<then> SPEC P"
  (* TODO: Move *)  
  lemma OBTAIN_nofail[refine_pw_simps]: "nofail (OBTAIN P) \<longleftrightarrow> (\<exists>x. P x)"
    unfolding OBTAIN_def
    by (auto simp: refine_pw_simps)
  lemma OBTAIN_inres[refine_pw_simps]: "inres (OBTAIN P) x \<longleftrightarrow> (\<forall>x. \<not>P x) \<or> P x"
    unfolding OBTAIN_def
    by (auto simp: refine_pw_simps)
  lemma OBTAIN_rule[refine_vcg]: "\<lbrakk> \<exists>x. P x; \<And>x. P x \<Longrightarrow> Q x  \<rbrakk> \<Longrightarrow> OBTAIN P \<le> SPEC Q"
    unfolding OBTAIN_def
    by auto
  lemma OBTAIN_refine_iff: "OBTAIN P \<le>\<Down>R (OBTAIN Q) \<longleftrightarrow> (Ex Q \<longrightarrow> Ex P \<and> Collect P \<subseteq> R\<inverse>``Collect Q)"
    unfolding OBTAIN_def by (auto simp: pw_le_iff refine_pw_simps)
  
  lemma OBTAIN_refine[refine]:
    assumes "RELATES R"
    assumes "\<And>x. Q x \<Longrightarrow> Ex P"
    assumes "\<And>x y. \<lbrakk>Q x; P y\<rbrakk> \<Longrightarrow> \<exists>x'. (y,x')\<in>R \<and> Q x'"
    shows "OBTAIN P \<le>\<Down>R (OBTAIN Q)"
    using assms unfolding OBTAIN_refine_iff 
    by blast
  
  definition "SELECT P \<equiv> if \<exists>x. P x then RES {Some x| x. P x} else RETURN None"
  lemma SELECT_rule[refine_vcg]:
    assumes "\<And>x. P x \<Longrightarrow> Q (Some x)"
    assumes "\<forall>x. \<not>P x \<Longrightarrow> Q None"
    shows "SELECT P \<le> SPEC Q"
    unfolding SELECT_def
    using assms
    by auto

  lemma SELECT_refine_iff: "(SELECT P \<le>\<Down>(\<langle>R\<rangle>option_rel) (SELECT P')) 
    \<longleftrightarrow> (  
      (Ex P' \<longrightarrow> Ex P) \<and>
      (\<forall>x. P x \<longrightarrow> (\<exists>x'. (x,x')\<in>R \<and> P' x'))
    )"  
    by (force simp: SELECT_def pw_le_iff refine_pw_simps) 

  lemma SELECT_refine[refine]:
    assumes "RELATES R"
    assumes "\<And>x'. P' x' \<Longrightarrow> \<exists>x. P x"
    assumes "\<And>x. P x \<Longrightarrow> \<exists>x'. (x,x')\<in>R \<and> P' x'"
    shows "SELECT P \<le>\<Down>(\<langle>R\<rangle>option_rel) (SELECT P')"
    unfolding SELECT_refine_iff using assms by blast


  lemma eq_or_mem_image_simp[simp]: "{f l |l. l = a \<or> l\<in>B} = insert (f a) {f l|l. l\<in>B}" by blast



  (* TODO: Move *)
  lemma LIST_FOREACH'_refine: "LIST_FOREACH' tsl' c' f' \<sigma>' \<le> LIST_FOREACH \<Phi> tsl' c' f' \<sigma>'"
    apply (rule refine_IdD)
    unfolding LIST_FOREACH_def LIST_FOREACH'_def
    apply refine_rcg
    apply simp
    apply (rule nfoldli_while)
    done

  lemma LIST_FOREACH'_eq: "LIST_FOREACH (\<lambda>_ _. True) tsl' c' f' \<sigma>' = (LIST_FOREACH' tsl' c' f' \<sigma>')"
    apply (rule antisym)
    subgoal
      apply (rule refine_IdD)
      unfolding LIST_FOREACH_def LIST_FOREACH'_def while_eq_nfoldli[symmetric] 
      apply (refine_rcg WHILEIT_refine_new_invar)
      unfolding WHILET_def
      apply (rule WHILEIT_refine_new_invar)

      apply refine_dref_type
      apply vc_solve
      unfolding FOREACH_body_def FOREACH_cond_def
      apply refine_vcg
      apply (auto simp: refine_pw_simps pw_le_iff neq_Nil_conv)
      done
    subgoal by (rule LIST_FOREACH'_refine)
    done


end
