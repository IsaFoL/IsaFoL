theory Completeness imports Unify begin

section {* Lifting Lemma *}

lemma lifting:
  assumes fin: "finite C \<and> finite D "
  assumes apart: "varsls C \<inter> varsls D = {}"
  assumes inst\<^sub>1: "instance_ofls C' C"
  assumes inst\<^sub>2: "instance_ofls D' D"
  assumes appl: "applicable C' D' L' M' \<sigma>"
  shows "\<exists>L M \<tau>. applicable C D L M \<tau> \<and>
                   instance_ofls (resolution C' D' L' M' \<sigma>) (resolution C D L M \<tau>)"
proof -
  let ?C'\<^sub>1 = "C' - L'"
  let ?D'\<^sub>1 = "D' - M'"

  from inst\<^sub>1 obtain lmbd where lmbd_p: "C {lmbd}\<^sub>l\<^sub>s = C'" unfolding instance_ofls_def by auto
  from inst\<^sub>2 obtain \<mu> where \<mu>_p: "D {\<mu>}\<^sub>l\<^sub>s = D'" unfolding instance_ofls_def by auto
  
  from \<mu>_p lmbd_p apart obtain \<eta> where \<eta>_p: "C {\<eta>}\<^sub>l\<^sub>s = C' \<and> D {\<eta>}\<^sub>l\<^sub>s = D'" using merge_sub by force

  from \<eta>_p have "\<exists>L \<subseteq> C. L {\<eta>}\<^sub>l\<^sub>s = L' \<and> (C - L){\<eta>}\<^sub>l\<^sub>s = ?C'\<^sub>1" using appl project_sub[of \<eta> C C' L'] unfolding applicable_def by auto
  then obtain L where L_p: "L \<subseteq> C \<and> L {\<eta>}\<^sub>l\<^sub>s = L' \<and> (C - L){\<eta>}\<^sub>l\<^sub>s = ?C'\<^sub>1" by auto
  let ?C\<^sub>1 = "C - L"

  from \<eta>_p have "\<exists>M \<subseteq> D. M {\<eta>}\<^sub>l\<^sub>s = M' \<and> (D - M){\<eta>}\<^sub>l\<^sub>s = ?D'\<^sub>1" using appl project_sub[of \<eta> D D' M'] unfolding applicable_def by auto
  then obtain M where M_p: "M \<subseteq> D \<and> M {\<eta>}\<^sub>l\<^sub>s = M' \<and> (D - M){\<eta>}\<^sub>l\<^sub>s = ?D'\<^sub>1" by auto
  let ?D\<^sub>1 = "D - M"

  from appl have "mguls \<sigma> (L' \<union> M'\<^sup>C)" unfolding applicable_def by auto
  then have "mguls \<sigma> (L {\<eta>}\<^sub>l\<^sub>s \<union> M {\<eta>}\<^sub>l\<^sub>s\<^sup>C)" using L_p M_p by auto
  then have "mguls \<sigma> ((L  \<union> M\<^sup>C) {\<eta>}\<^sub>l\<^sub>s)" using compls_subls subls_union by auto
  then have "unifierls \<sigma> ((L  \<union> M\<^sup>C) {\<eta>}\<^sub>l\<^sub>s)" unfolding mguls_def by auto
  then have \<eta>\<sigma>uni: "unifierls (\<eta> \<cdot> \<sigma>) (L  \<union> M\<^sup>C)" 
    unfolding unifierls_def using composition_conseq2l by auto
  then obtain \<tau> where \<tau>_p: "mguls \<tau> (L  \<union> M\<^sup>C)" using unification fin by (meson L_p M_p finite_UnI finite_imageI rev_finite_subset) 
  then obtain \<phi> where \<phi>_p: "\<tau> \<cdot> \<phi> = \<eta> \<cdot> \<sigma>" using \<eta>\<sigma>uni unfolding mguls_def by auto
  
  (* Showing that we have the desired resolvent *)
  let ?E = "((C - L)  \<union> (D - M)) {\<tau>}\<^sub>l\<^sub>s"
  have "?E {\<phi>}\<^sub>l\<^sub>s  = (?C\<^sub>1 \<union> ?D\<^sub>1 ) {\<tau> \<cdot> \<phi>}\<^sub>l\<^sub>s" using subls_union composition_conseq2ls by auto
  also have "... = (?C\<^sub>1 \<union> ?D\<^sub>1 ) {\<eta> \<cdot> \<sigma>}\<^sub>l\<^sub>s" using \<phi>_p by auto
  also have "... = (?C\<^sub>1 {\<eta>}\<^sub>l\<^sub>s \<union> ?D\<^sub>1 {\<eta>}\<^sub>l\<^sub>s) {\<sigma>}\<^sub>l\<^sub>s" using subls_union composition_conseq2ls by auto
  also have "... = (?C'\<^sub>1 \<union> ?D'\<^sub>1) {\<sigma>}\<^sub>l\<^sub>s" using \<eta>_p L_p M_p by auto
  finally have "?E {\<phi>}\<^sub>l\<^sub>s = ((C' - L') \<union> (D' - M')){\<sigma>}\<^sub>l\<^sub>s" by auto
  then have inst: "instance_ofls (resolution C' D' L' M' \<sigma>) (resolution C D L M \<tau>) "
    unfolding resolution_def instance_ofls_def by blast

  (* Showing that the resolution is applicable: *)
  {
    have "C' \<noteq> {}" using appl unfolding applicable_def by auto
    then have "C \<noteq> {}" using \<eta>_p by auto
  } moreover {
    have "D' \<noteq> {}" using appl unfolding applicable_def by auto
    then have "D \<noteq> {}" using \<eta>_p by auto
  } moreover {
    have "L' \<noteq> {}" using appl unfolding applicable_def by auto
    then have "L \<noteq> {}" using L_p by auto
  } moreover {
    have "M' \<noteq> {}" using appl unfolding applicable_def by auto
    then have "M \<noteq> {}" using M_p by auto
  }
  ultimately have appll: "applicable C D L M \<tau>" 
    using apart L_p M_p \<tau>_p unfolding applicable_def by auto

  from inst appll show ?thesis by auto
qed


section {* Completeness *}
(* assumes openb: "\<forall>T. \<exists>G. open_branch G T Cs" assumes finite_cs: "finite Cs" "\<forall>C\<in>Cs. finite C" shows "\<exists>G. evalcs HFun G Cs" *)

lemma falsifiesg_empty: (* Maybe move to partial interpretation section *)
  assumes "falsifiesg [] C"
  shows "C = {}"
proof -
  have "\<forall>l \<in> C. False"
    proof
      fix l
      assume "l\<in>C"
      then have "falsifiesl [] l" using assms by auto
      then show False by (cases l) auto
    qed
  then show ?thesis by auto
qed

lemma falsifiescs_empty:  (* Maybe move to partial interpretation section *)
  assumes "falsifiesc [] C"
  shows "C = {}"
proof -
  from assms obtain C' where C'_p: "instance_ofls C' C \<and> falsifiesg [] C'" by auto
  then have "C'= {}" using falsifiesg_empty by auto
  then show "C = {}" using C'_p unfolding instance_ofls_def by auto
qed

lemma complements_do_not_falsify':
  assumes l1C1': "l1 \<in> C1'"
  assumes l2C1': "l2 \<in> C1'"
  assumes comp: "l1 = l2\<^sup>c"
  assumes falsif: "falsifiesg G C1'"
  shows "False"
proof (cases l1)
  case (Pos p ts)
  from assms have gr: "groundl l1" using falsifies_ground by auto
  then have Neg: "l2 = Neg p ts" using comp Pos by (cases l2) auto

  from falsif have "falsifiesl G l1" using l1C1' by auto
  then have "\<exists>i. G ! i = False \<and> fatom_from_nat i = Pos p ts" using l1C1' Pos by auto 
  then obtain i where "G ! i = False \<and> fatom_from_nat i = Pos p ts" by auto
  then have "G ! nat_from_fatom (Pos p ts) = False" using fatom_from_nat_is_nat_from_fatom gr Pos by auto
  moreover
  from falsif have "falsifiesl G l2" using l2C1' by auto
  then have "\<exists>i. G ! i = True \<and> fatom_from_nat i = Pos p ts" using l2C1' Neg by auto 
  then obtain i where "G ! i = True \<and> fatom_from_nat i = Pos p ts" by auto
  then have "G ! nat_from_fatom (Pos p ts) = True" using fatom_from_nat_is_nat_from_fatom gr Pos by auto
  ultimately show ?thesis by auto
next
  case (Neg p ts) (* Symmetrical *)
  from assms have gr: "groundl l1" using falsifies_ground by auto
  then have Pos: "l2 = Pos p ts" using comp Neg by (cases l2) auto

  from falsif have "falsifiesl G l1" using l1C1' by auto
  then have "\<exists>i. G ! i = True \<and> fatom_from_nat i = Pos p ts" using l1C1' Neg by auto 
  then obtain i where "G ! i = True \<and> fatom_from_nat i = Pos p ts" by auto
  then have "G ! nat_from_fatom (Pos p ts) = True" using fatom_from_nat_is_nat_from_fatom gr Neg by auto
  moreover
  from falsif have "falsifiesl G l2" using l2C1' by auto
  then have "\<exists>i. G ! i = False \<and> fatom_from_nat i = Pos p ts" using l2C1' Pos by auto 
  then obtain i where "G ! i = False \<and> fatom_from_nat i = Pos p ts" by auto
  then have "G ! nat_from_fatom (Pos p ts) = False" using fatom_from_nat_is_nat_from_fatom gr Neg by auto
  ultimately show ?thesis by auto
qed

lemma complements_do_not_falsify:
  assumes l1C1': "l1 \<in> C1'"
  assumes l2C1': "l2 \<in> C1'"
  assumes fals: "falsifiesg G C1'"
  shows "l1 \<noteq> l2\<^sup>c"
using assms complements_do_not_falsify' by blast


lemma number_lemma:
  assumes "\<not>(\<exists>i. i < length B \<and> P(i))"
  assumes "\<exists>i. i < length (B@[d]) \<and> P(i)"
  shows "P(length B)"
using assms less_Suc_eq by auto

lemma other_falsified:
  assumes C1'_p: "groundls C1' \<and> falsifiesg (B@[d]) C1'" 
  assumes l_p: "l \<in> C1'" "nat_from_fatom l = length B"
  assumes other: "lo \<in> C1'" "lo \<noteq> l"
  shows "falsifiesl B lo"
proof -
  have ground_l2: "groundl l" using l_p C1'_p by auto
  (* They are, of course, also ground *)
  have ground_lo: "groundl lo" using C1'_p other by auto
  from C1'_p have "falsifiesg (B@[d]) (C1' - {l})" by auto
  (* And indeed, falsified by B2 *)
  then have loB2: "falsifiesl (B@[d]) lo" using other by auto
  then obtain i where "fatom_from_nat i = Pos (get_pred lo) (get_terms lo) \<and> i < length (B @ [True])" by (cases lo) auto
  then have "nat_from_fatom (fatom_from_nat i) = nat_from_fatom (Pos (get_pred lo) (get_terms lo)) \<and> i < length (B @ [True])" by auto
  (* And they have numbers in the range of B2, i.e. less than B + 1*)
  then have "nat_from_fatom lo < length B + 1" using undiag_neg undiag_diag_fatom by (cases lo) auto
  moreover
  have l_lo: "l\<noteq>lo" using other by auto
  (* The are not the complement of l2, since then the clause could not be falsified *)
  have lc_lo: "lo \<noteq> l\<^sup>c" using C1'_p l_p other complements_do_not_falsify[of lo C1' l "(B@[d])"] by auto
  from l_lo lc_lo have "get_pred l \<noteq> get_pred lo \<or> get_terms l \<noteq> get_terms lo" using literal.expand sign_comp by blast
  then have "nat_from_fatom lo \<noteq> nat_from_fatom l" using nat_from_fatom_inj_mod_sign ground_lo ground_l2 by metis
  (* Therefore they have different numbers *)
  then have "nat_from_fatom lo \<noteq> length B" using l_p by auto
  ultimately 
  (* So their numbers are in the range of B *)
  have "nat_from_fatom lo < length B" by auto
  (* So we did not need the last index of B2 to falsify them, i.e. B suffices *)
  then show "falsifiesl B lo" using loB2 shorter_falsifiesl by blast
qed


theorem completeness':
  shows "closed_tree T Cs \<Longrightarrow> \<forall>C\<in>Cs. finite C \<Longrightarrow> \<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'"
proof (induction T arbitrary: Cs rule: measure_induct_rule[of treesize])
  fix T::tree
  fix Cs :: "fterm clause set"
  assume ih: "(\<And>T' Cs. treesize T' < treesize T \<Longrightarrow> closed_tree T' Cs \<Longrightarrow> \<forall>C\<in>Cs. finite C \<Longrightarrow>
                 \<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs')"
  assume clo: "closed_tree T Cs"
  assume finite_Cs: "\<forall>C\<in>Cs. finite C"
  
  { (* Base case *)
    assume "treesize T = 0"
    then have "T=Leaf" using treesize_Leaf by auto
    then have "closed_branch [] Leaf Cs" using branch_inv_Leaf clo by auto
    then have "falsifiescs [] Cs" by auto
    then have "{} \<in> Cs" using falsifiescs_empty by auto
    then have "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'" unfolding resolution_deriv_def by auto
  }
  moreover
  { (* Induction case *)
    assume "treesize T > 0"
    then have "\<exists>l r. T=Branching l r" by (cases T) auto
    
    (* Finding sibling branches and their corresponding clauses *)
    then obtain B where b_p: "internal B T \<and> branch (B@[True]) T \<and> branch (B@[False]) T"
      using internal_branch[of _ "[]" _ T] Branching_Leaf_Leaf_Tree by fastforce 
    let ?B1 = "B@[True]"
    let ?B2 = "B@[False]"

    obtain C1o where C1o_p: "C1o \<in> Cs \<and> falsifiesc ?B1 C1o" using b_p clo by fastforce 
    obtain C2o where C2o_p: "C2o \<in> Cs \<and> falsifiesc ?B2 C2o" using b_p clo by (meson closed_tree.simps) 

    (* Standardizing the clauses apart *)
    let ?C1 = "fst (std_apart C1o C2o)"
    let ?C2 = "snd (std_apart C1o C2o)"
    have C1_p: "falsifiesc ?B1 ?C1" using std_apart_falsifies1[of C1o C2o ?C1 ?C2 ?B1] C1o_p by auto
    have C2_p: "falsifiesc ?B2 ?C2" using std_apart_falsifies2[of C1o C2o ?C1 ?C2 ?B2] C2o_p by auto

    have fin: "finite ?C1 \<and> finite ?C2" using C1o_p C2o_p finite_std_apart[of C1o C2o ?C1 ?C2] finite_Cs by auto

    (* We go down to the ground world: *)
    (* Finding the falsifying ground instance C1' of C1, and proving properties about it *)
    
    (* C1' is falsified by B1: *)
    from C1_p  obtain C1' where C1'_p: "groundls C1' \<and> instance_ofls C1' ?C1 \<and> falsifiesg ?B1 C1'" 
      using falsifiesc_ground[of ?C1 ?B1] by metis

    have "\<not>falsifiesc B C1o" using C1o_p b_p clo by auto
    then have "\<not>falsifiesc B ?C1" using std_apart_falsifies1_sym[of C1o C2o ?C1 ?C2 B] by auto
    (* C1' is not falsified by B *)
    then have l_B: "\<not>falsifiesg B C1'" using C1'_p by auto

    (* C1' contains a literal l1 that is falsified by B1, but not B *)
    from C1'_p l_B obtain l1 where l1_p: "l1 \<in> C1' \<and> falsifiesl (B@[True]) l1 \<and> \<not>(falsifiesl B l1)" by auto

    then have "\<not>(\<exists>i.
      i < length B
      \<and> B ! i = (\<not>sign l1)
      \<and> fatom_from_nat i = Pos (get_pred l1) (get_terms l1))" by (induction l1) auto
    then have "\<not>(\<exists>i.
      i < length B
      \<and> (B@[True]) ! i = (\<not>sign l1)
      \<and> fatom_from_nat i = Pos (get_pred l1) (get_terms l1))" by (metis nth_append) (* Not falsified by B *)
    moreover
    (* l1 is, of course, ground *)
    have ground_l1: "groundl l1" using C1'_p l1_p by auto
    then have "\<exists>i.  
      i < length (B@[True])
      \<and> (B@[True]) ! i = (\<not>sign l1)
      \<and> fatom_from_nat i = Pos (get_pred l1) (get_terms l1)" using ground_falsifies l1_p by blast (* falsified by B1 *)
    ultimately
    have l1_sign_no: "(B@[True]) ! (length B) = (\<not>sign l1) \<and> fatom_from_nat (length B) = Pos (get_pred l1) (get_terms l1)"
      using number_lemma[of B "\<lambda>i. (B @ [True]) ! i = (\<not> sign l1) \<and> fatom_from_nat i = Pos (get_pred l1) (get_terms l1)"] by auto

    (* l1 is negative *)
    from l1_sign_no have l1_sign: "sign l1 = False" by auto
    from l1_sign_no have "nat_from_fatom (Pos (get_pred l1) (get_terms l1)) = length B" using undiag_diag_fatom by metis
    (* l1 is literal no (length B) *)
    then have l1_no: "nat_from_fatom l1 = length B" using undiag_neg[of "get_pred l1" "get_terms l1"] undiag_diag_fatom by (cases l1) auto

    (* All the other literals in C1' must be falsified by B, since they are falsified by B1, but not l1. *)
    from C1'_p l1_no l1_p have B_C1'l1: "falsifiesg B (C1' - {l1})" (* This should be a lemma *)
      using other_falsified by blast



    (* We do the same exercise for C2, C2', B2, l2 *)
    from C2_p obtain C2' where C2'_p: "groundls C2' \<and> instance_ofls C2' ?C2 \<and> falsifiesg ?B2 C2'" 
       using falsifiesc_ground[of ?C2 ?B2] by metis

    have "\<not>falsifiesc B C2o" using C2o_p b_p clo by auto
    then have "\<not>falsifiesc B ?C2" using std_apart_falsifies2_sym[of C1o C2o ?C1 ?C2 B] by auto
    then have l_B: "\<not>falsifiesg B C2'" using C2'_p by auto (* I already had something called l_B... I should give it a new name *)
    
    (* C2' contains a literal l2 that is falsified by B2, but not B *)
    from C2'_p l_B obtain l2 where l2_p: "l2 \<in> C2' \<and> falsifiesl (B@[False]) l2 \<and> \<not>(falsifiesl B l2)" by auto

    then have "\<not>(\<exists>i.  
      i < length B
      \<and> B ! i = (\<not>sign l2)
      \<and> fatom_from_nat i = Pos (get_pred l2) (get_terms l2))" by (cases l2) auto
    then have "\<not>(\<exists>i.  
      i < length B
      \<and> (B@[False]) ! i = (\<not>sign l2)
      \<and> fatom_from_nat i = Pos (get_pred l2) (get_terms l2))" by (metis nth_append)
    moreover
    (* l2 is, of course, ground *)
    have ground_l2: "groundl l2" using C2'_p l2_p by auto
    then have "\<exists>i.  
      i < length (B@[False])
      \<and> (B@[False]) ! i = (\<not>sign l2)
      \<and> fatom_from_nat i = Pos (get_pred l2) (get_terms l2)" using ground_falsifies l2_p by blast
    ultimately
    have l2_sign_no: "(B@[False]) ! (length B) = (\<not>sign l2) \<and> fatom_from_nat (length B) = Pos (get_pred l2) (get_terms l2)"
      using number_lemma[of B "\<lambda>i. (B @ [False]) ! i = (\<not> sign l2) \<and> fatom_from_nat i = Pos (get_pred l2) (get_terms l2)"] by auto

    (* l2 is positive *)
    from l2_sign_no have l2_sign: "sign l2 = True" by auto
    from l2_sign_no have "nat_from_fatom (Pos (get_pred l2) (get_terms l2)) = length B" using undiag_diag_fatom by metis
    (* l2 is literal no (length B) *)
    then have l2_no: "nat_from_fatom l2 = length B" using undiag_neg[of "get_pred l2" "get_terms l2"] l2_sign undiag_diag_fatom by auto

    (* All the other literals in C2' must be falsified by B, since they are falsified by B2, but not l2. *)
    from C2'_p l2_no l2_p have B_C2'l2: "falsifiesg B (C2' - {l2})"
      using other_falsified by blast

    (* Proving some properties about C1' and C2', l1 and l2, as well as the resolvent of C1' and C2' *)
    have l2cisl1: "l2\<^sup>c = l1" (* Could perhaps be a lemma *)
      proof -
        from l1_no l2_no ground_l1 ground_l2 have "get_pred l1 = get_pred l2" using nat_from_fatom_inj_mod_sign by auto
        moreover
        from l1_no l2_no ground_l1 ground_l2 have "get_terms l1 = get_terms l2" using nat_from_fatom_inj_mod_sign by auto
        ultimately show "l2\<^sup>c = l1" using l1_sign l2_sign using sign_comp by metis 
      qed
    
    have "applicable C1' C2' {l1} {l2} Resolution.\<epsilon>" unfolding applicable_def
      using l1_p l2_p C1'_p groundls_varsls l2cisl1 empty_comp2 unfolding mguls_def unifierls_def by auto
    (* Lifting to get a resolvent of C1 and C2 *)
    then obtain L1 L2 \<tau> where L1L2\<tau>_p: "applicable ?C1 ?C2 L1 L2 \<tau>  \<and> instance_ofls (resolution C1' C2' {l1} {l2} Resolution.\<epsilon>) (resolution ?C1 ?C2 L1 L2 \<tau>)"
      using std_apart_apart' C1'_p C2'_p lifting[of ?C1 ?C2 C1' C2' "{l1}" "{l2}" Resolution.\<epsilon>] fin by auto


    (* Defining the clause to be derived, the new clausal form and the new tree *)
    (* We name the resolvent C *)
    obtain C where C_p: "C=resolution ?C1 ?C2 L1 L2 \<tau>" by auto
    obtain CsNext where CsNext_p: "CsNext = Cs \<union> {?C1, ?C2, C}" by auto
    obtain T'' where T''_p: "T'' = delete B T" by auto (* Here we delete the two branch children B1 and B2 of B *)
    
    (* Our new clause is falsified by the branch B of our new tree *)
    have "falsifiesg B ((C1' - {l1}) \<union> (C2' - {l2}))" using B_C1'l1 B_C2'l2 by cases auto
    then have "falsifiesg B (resolution C1' C2' {l1} {l2} Resolution.\<epsilon>)" unfolding resolution_def empty_subls by auto
    then have falsifies_C: "falsifiesc B C" using C_p L1L2\<tau>_p by auto

    have T''_smaller: "treesize T'' < treesize T" using treezise_delete T''_p b_p by auto
    have T''_bran: "anybranch T'' (\<lambda>b. closed_branch b T'' CsNext)"
      proof (rule allI; rule impI)
        fix b
        assume br: "branch b T''"
        from br have "b = B \<or> branch b T" using branch_delete T''_p by auto
        then show "closed_branch b T'' CsNext"
          proof
            assume "b=B"
            then show "closed_branch b T'' CsNext" using falsifies_C br CsNext_p by auto
          next
            assume "branch b T"
            then show "closed_branch b T'' CsNext" using clo br T''_p CsNext_p by auto
          qed
      qed
    then have T''_bran2: "anybranch T'' (\<lambda>b. falsifiescs b CsNext)" by auto (* replace T''_bran with this maybe? *)

    (* We cut the tree even smaller to ensure only the branches are falsified, i.e. it is a closed tree *)
    obtain T' where T'_p: "T' = cutoff (\<lambda>G. falsifiescs G CsNext) [] T''" by auto
    have T'_smaller: "treesize T' < treesize T" using treesize_cutoff[of "\<lambda>G. falsifiescs G CsNext" "[]" T''] T''_smaller unfolding T'_p by auto

    from T''_bran2 have "anybranch T' (\<lambda>b. falsifiescs b CsNext)" using cutoff_branch[of T'' "\<lambda>b. falsifiescs b CsNext"] T'_p by auto
    then have T'_bran: "anybranch T' (\<lambda>b. closed_branch b T' CsNext)" by auto
    have T'_intr: "anyinternal T' (\<lambda>p. \<not>falsifiescs p CsNext)" using T'_p cutoff_internal[of T'' "\<lambda>b. falsifiescs b CsNext"] T''_bran2 by blast
    have T'_closed: "closed_tree T' CsNext" using T'_bran T'_intr by auto
    have finite_CsNext: "\<forall>C\<in>CsNext. finite C" unfolding CsNext_p C_p resolution_def using finite_Cs fin by auto

    (* By induction hypothesis we get a resolution derivation of {} from our new clausal form *)
    from T'_smaller T'_closed have "\<exists>Cs''. resolution_deriv CsNext Cs'' \<and> {} \<in> Cs''" using ih[of T' CsNext] finite_CsNext by blast
    then obtain Cs'' where Cs''_p: "resolution_deriv CsNext Cs'' \<and> {} \<in> Cs''" by auto
    moreover
    { (* Proving that we can actually derive the new clausal form *)
      have "resolution_step Cs (Cs \<union> {?C1})" using std_apart_renames1'[of C1o C2o] standardize_apart C1o_p by (metis Un_insert_right prod.collapse)
      moreover
      have "resolution_step (Cs \<union> {?C1}) (Cs \<union> {?C1} \<union> {?C2})" using std_apart_renames2'[of C1o C2o] standardize_apart C2o_p by (metis Un_insert_right insert_iff prod.collapse sup_bot.right_neutral)
      then have "resolution_step (Cs \<union> {?C1}) (Cs \<union> {?C1,?C2})" by (metis insert_is_Un sup_assoc)
      moreover
      then have "resolution_step (Cs \<union> {?C1,?C2}) (Cs \<union> {?C1,?C2} \<union> {C})" 
        using L1L2\<tau>_p resolution_rule[of ?C1 "Cs \<union> {?C1,?C2}" ?C2 L1 L2 \<tau> ] using C_p by auto
      then have "resolution_step (Cs \<union> {?C1,?C2}) CsNext"by (metis CsNext_p insert_is_Un sup_assoc) 
      ultimately
      have "resolution_deriv Cs CsNext"  unfolding resolution_deriv_def by auto
    }
    (* Combining the two derivations, we get the desired derivation from Cs of {} *)
    ultimately have "resolution_deriv Cs Cs''"  unfolding resolution_deriv_def by auto
    then have "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'" using Cs''_p by auto
  }
  ultimately show "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'" by auto
qed

theorem completeness:
  assumes finite_cs: "finite Cs" "\<forall>C\<in>Cs. finite C"
  assumes unsat: "\<forall>(F::hterm fun_denot) (G::hterm pred_denot) . \<not>evalcs F G Cs"
  shows "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'"
proof -
  from unsat have "\<forall>(G::hterm pred_denot) . \<not>evalcs HFun G Cs" by auto
  then obtain T where "closed_tree T Cs" using herbrand assms by blast
  then show "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'" using completeness' assms by auto
qed

(* To get rid of the type - something like - find a countable subset using CHOICE *)
end