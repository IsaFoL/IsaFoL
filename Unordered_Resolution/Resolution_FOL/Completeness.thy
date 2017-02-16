section {* Lifting Lemma *}

theory Completeness imports Resolution begin

locale unification =
  assumes unification: "\<And>\<sigma> L. finite L \<Longrightarrow> unifier\<^sub>l\<^sub>s \<sigma> L \<Longrightarrow> \<exists>\<theta>. mgu\<^sub>l\<^sub>s \<theta> L"
begin
text {*
  A proof of this assumption is available \cite{unify} in the IsaFoL project \cite{isafol}.
  It uses a similar theorem from the IsaFoR \cite{isafor} project.
*}


lemma lifting:
  assumes fin: "finite C \<and> finite D "
  assumes apart: "vars\<^sub>l\<^sub>s C \<inter> vars\<^sub>l\<^sub>s D = {}"
  assumes inst\<^sub>1: "instance_of\<^sub>l\<^sub>s C' C"
  assumes inst\<^sub>2: "instance_of\<^sub>l\<^sub>s D' D"
  assumes appl: "applicable C' D' L' M' \<sigma>"
  shows "\<exists>L M \<tau>. applicable C D L M \<tau> \<and>
                   instance_of\<^sub>l\<^sub>s (resolution C' D' L' M' \<sigma>) (resolution C D L M \<tau>)"
proof -
  let ?C'\<^sub>1 = "C' - L'"
  let ?D'\<^sub>1 = "D' - M'"

  from inst\<^sub>1 obtain lmbd where lmbd_p: "C \<cdot>\<^sub>l\<^sub>s lmbd = C'" unfolding instance_of\<^sub>l\<^sub>s_def by auto
  from inst\<^sub>2 obtain \<mu> where \<mu>_p: "D \<cdot>\<^sub>l\<^sub>s \<mu> = D'" unfolding instance_of\<^sub>l\<^sub>s_def by auto
  
  from \<mu>_p lmbd_p apart obtain \<eta> where \<eta>_p: "C \<cdot>\<^sub>l\<^sub>s \<eta> = C' \<and> D \<cdot>\<^sub>l\<^sub>s \<eta> = D'" using merge_sub by force

  from \<eta>_p have "\<exists>L \<subseteq> C. L \<cdot>\<^sub>l\<^sub>s \<eta> = L' \<and> (C - L) \<cdot>\<^sub>l\<^sub>s \<eta> = ?C'\<^sub>1" using appl project_sub[of \<eta> C C' L'] unfolding applicable_def by auto
  then obtain L where L_p: "L \<subseteq> C \<and> L \<cdot>\<^sub>l\<^sub>s \<eta> = L' \<and> (C - L) \<cdot>\<^sub>l\<^sub>s \<eta> = ?C'\<^sub>1" by auto
  let ?C\<^sub>1 = "C - L"

  from \<eta>_p have "\<exists>M \<subseteq> D. M \<cdot>\<^sub>l\<^sub>s \<eta> = M' \<and> (D - M) \<cdot>\<^sub>l\<^sub>s \<eta> = ?D'\<^sub>1" using appl project_sub[of \<eta> D D' M'] unfolding applicable_def by auto
  then obtain M where M_p: "M \<subseteq> D \<and> M \<cdot>\<^sub>l\<^sub>s \<eta> = M' \<and> (D - M) \<cdot>\<^sub>l\<^sub>s \<eta> = ?D'\<^sub>1" by auto
  let ?D\<^sub>1 = "D - M"

  from appl have "mgu\<^sub>l\<^sub>s \<sigma> (L' \<union> M'\<^sup>C)" unfolding applicable_def by auto
  then have "mgu\<^sub>l\<^sub>s \<sigma> ((L \<cdot>\<^sub>l\<^sub>s \<eta>) \<union> (M \<cdot>\<^sub>l\<^sub>s \<eta>)\<^sup>C)" using L_p M_p by auto
  then have "mgu\<^sub>l\<^sub>s \<sigma> ((L  \<union> M\<^sup>C) \<cdot>\<^sub>l\<^sub>s \<eta>)" using compls_subls subls_union by auto
  then have "unifier\<^sub>l\<^sub>s \<sigma> ((L  \<union> M\<^sup>C) \<cdot>\<^sub>l\<^sub>s \<eta>)" unfolding mgu\<^sub>l\<^sub>s_def by auto
  then have \<eta>\<sigma>uni: "unifier\<^sub>l\<^sub>s (\<eta> \<cdot> \<sigma>) (L  \<union> M\<^sup>C)" 
    unfolding unifier\<^sub>l\<^sub>s_def using composition_conseq2l by auto
  then obtain \<tau> where \<tau>_p: "mgu\<^sub>l\<^sub>s \<tau> (L  \<union> M\<^sup>C)" using unification fin by (meson L_p M_p finite_UnI finite_imageI rev_finite_subset) 
  then obtain \<phi> where \<phi>_p: "\<tau> \<cdot> \<phi> = \<eta> \<cdot> \<sigma>" using \<eta>\<sigma>uni unfolding mgu\<^sub>l\<^sub>s_def by auto
  
  -- {* Showing that we have the desired resolvent: *}
  let ?E = "((C - L)  \<union> (D - M)) \<cdot>\<^sub>l\<^sub>s \<tau>"
  have "?E \<cdot>\<^sub>l\<^sub>s \<phi>  = (?C\<^sub>1 \<union> ?D\<^sub>1 ) \<cdot>\<^sub>l\<^sub>s (\<tau> \<cdot> \<phi>)" using subls_union composition_conseq2ls by auto
  also have "... = (?C\<^sub>1 \<union> ?D\<^sub>1 ) \<cdot>\<^sub>l\<^sub>s (\<eta> \<cdot> \<sigma>)" using \<phi>_p by auto
  also have "... = ((?C\<^sub>1 \<cdot>\<^sub>l\<^sub>s \<eta>) \<union> (?D\<^sub>1 \<cdot>\<^sub>l\<^sub>s \<eta>)) \<cdot>\<^sub>l\<^sub>s \<sigma>" using subls_union composition_conseq2ls by auto
  also have "... = (?C'\<^sub>1 \<union> ?D'\<^sub>1) \<cdot>\<^sub>l\<^sub>s \<sigma>" using \<eta>_p L_p M_p by auto
  finally have "?E \<cdot>\<^sub>l\<^sub>s \<phi> = ((C' - L') \<union> (D' - M')) \<cdot>\<^sub>l\<^sub>s \<sigma>" by auto
  then have inst: "instance_of\<^sub>l\<^sub>s (resolution C' D' L' M' \<sigma>) (resolution C D L M \<tau>) "
    unfolding resolution_def instance_of\<^sub>l\<^sub>s_def by blast

  -- {* Showing that the resolution is applicable: *}
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

lemma falsifies\<^sub>g_empty:
  assumes "falsifies\<^sub>g [] C"
  shows "C = {}"
proof -
  have "\<forall>l \<in> C. False"
    proof
      fix l
      assume "l\<in>C"
      then have "falsifies\<^sub>l [] l" using assms by auto
      then show False unfolding falsifies\<^sub>l_def by (cases l) auto
    qed
  then show ?thesis by auto
qed

lemma falsifies\<^sub>c\<^sub>s_empty:
  assumes "falsifies\<^sub>c [] C"
  shows "C = {}"
proof -
  from assms obtain C' where C'_p: "instance_of\<^sub>l\<^sub>s C' C \<and> falsifies\<^sub>g [] C'" by auto
  then have "C'= {}" using falsifies\<^sub>g_empty by auto
  then show "C = {}" using C'_p unfolding instance_of\<^sub>l\<^sub>s_def by auto
qed

lemma complements_do_not_falsify':
  assumes l1C1': "l\<^sub>1 \<in> C\<^sub>1'"
  assumes l\<^sub>2C1': "l\<^sub>2 \<in> C\<^sub>1'"
  assumes comp: "l\<^sub>1 = l\<^sub>2\<^sup>c"
  assumes falsif: "falsifies\<^sub>g G C\<^sub>1'"
  shows "False"
proof (cases l\<^sub>1)
  case (Pos p ts)
  let ?i1 = "nat_from_fatom (p, ts)"

  from assms have gr: "ground\<^sub>l l\<^sub>1" unfolding falsifies\<^sub>l_def by auto
  then have Neg: "l\<^sub>2 = Neg p ts" using comp Pos by (cases l\<^sub>2) auto

  from falsif have "falsifies\<^sub>l G l\<^sub>1" using l1C1' by auto
  then have "G ! ?i1 = False" using l1C1' Pos unfolding falsifies\<^sub>l_def by (induction "Pos p ts") auto
  moreover
  let ?i2 = "nat_from_fatom (get_atom l\<^sub>2)"
  from falsif have "falsifies\<^sub>l G l\<^sub>2" using l\<^sub>2C1' by auto
  then have "G ! ?i2 = (\<not>sign l\<^sub>2)" unfolding falsifies\<^sub>l_def by meson
  then have "G ! ?i1 = (\<not>sign l\<^sub>2)" using Pos Neg comp by simp
  then have "G ! ?i1 = True" using Neg by auto
  ultimately show ?thesis by auto
next
  case (Neg p ts)
  let ?i1 = "nat_from_fatom (p,ts)"

  from assms have gr: "ground\<^sub>l l\<^sub>1" unfolding falsifies\<^sub>l_def by auto
  then have Pos: "l\<^sub>2 = Pos p ts" using comp Neg by (cases l\<^sub>2) auto

  from falsif have "falsifies\<^sub>l G l\<^sub>1" using l1C1' by auto
  then have "G ! ?i1 = True" using l1C1' Neg unfolding falsifies\<^sub>l_def by (metis get_atom.simps(2) literal.disc(2)) 
  moreover
  let ?i2 = "nat_from_fatom (get_atom l\<^sub>2)"
  from falsif have "falsifies\<^sub>l G l\<^sub>2" using l\<^sub>2C1' by auto
  then have "G ! ?i2 = (\<not>sign l\<^sub>2)" unfolding falsifies\<^sub>l_def by meson
  then have "G ! ?i1 = (\<not>sign l\<^sub>2)" using Pos Neg comp by simp
  then have "G ! ?i1 = False" using Pos using literal.disc(1) by blast
  ultimately show ?thesis by auto
qed

lemma complements_do_not_falsify:
  assumes l1C1': "l\<^sub>1 \<in> C\<^sub>1'"
  assumes l\<^sub>2C1': "l\<^sub>2 \<in> C\<^sub>1'"
  assumes fals: "falsifies\<^sub>g G C\<^sub>1'"
  shows "l\<^sub>1 \<noteq> l\<^sub>2\<^sup>c"
using assms complements_do_not_falsify' by blast

lemma other_falsified:
  assumes C1'_p: "ground\<^sub>l\<^sub>s C\<^sub>1' \<and> falsifies\<^sub>g (B@[d]) C\<^sub>1'" 
  assumes l_p: "l \<in> C\<^sub>1'" "nat_from_fatom (get_atom l) = length B"
  assumes other: "lo \<in> C\<^sub>1'" "lo \<noteq> l"
  shows "falsifies\<^sub>l B lo"
proof -
  let ?i = "nat_from_fatom (get_atom lo)"
  have ground_l\<^sub>2: "ground\<^sub>l l" using l_p C1'_p by auto
  -- {* They are, of course, also ground: *}
  have ground_lo: "ground\<^sub>l lo" using C1'_p other by auto
  from C1'_p have "falsifies\<^sub>g (B@[d]) (C\<^sub>1' - {l})" by auto
  -- {* And indeed, falsified by @{term "B@[d]"}: *}
  then have loB\<^sub>2: "falsifies\<^sub>l (B@[d]) lo" using other by auto
  then have "?i < length (B @ [d])" unfolding falsifies\<^sub>l_def by meson
  -- {* And they have numbers in the range of @{term "B@[d]"}, i.e. less than @{term "length B + 1"}: *}
  then have "nat_from_fatom (get_atom lo) < length B + 1" using undiag_diag_fatom by (cases lo) auto
  moreover
  have l_lo: "l\<noteq>lo" using other by auto
  -- {* The are not the complement of @{term l }, since then the clause could not be falsified: *}
  have lc_lo: "lo \<noteq> l\<^sup>c" using C1'_p l_p other complements_do_not_falsify[of lo C\<^sub>1' l "(B@[d])"] by auto
  from l_lo lc_lo have "get_atom l \<noteq> get_atom lo" using sign_comp_atom by metis
  then have "nat_from_fatom (get_atom lo) \<noteq> nat_from_fatom (get_atom l)" 
    using nat_from_fatom_bij ground_lo ground_l\<^sub>2 ground\<^sub>l_ground_fatom 
    unfolding bij_betw_def inj_on_def by metis
  -- {* Therefore they have different numbers: *}
  then have "nat_from_fatom (get_atom lo) \<noteq> length B" using l_p by auto
  ultimately 
  -- {* So their numbers are in the range of @{term B}: *}
  have "nat_from_fatom (get_atom lo) < length B" by auto
  -- {* So we did not need the last index of @{term "B@[d]"} to falsify them, i.e. @{term B} suffices: *}
  then show "falsifies\<^sub>l B lo" using loB\<^sub>2 shorter_falsifies\<^sub>l by blast
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
  
  { -- {* Base case: *}
    assume "treesize T = 0"
    then have "T=Leaf" using treesize_Leaf by auto
    then have "closed_branch [] Leaf Cs" using branch_inv_Leaf clo unfolding closed_tree_def by auto
    then have "falsifies\<^sub>c\<^sub>s [] Cs" by auto
    then have "{} \<in> Cs" using falsifies\<^sub>c\<^sub>s_empty by auto
    then have "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'" unfolding resolution_deriv_def by auto
  }
  moreover
  { -- {* Induction case: *}
    assume "treesize T > 0"
    then have "\<exists>l r. T=Branching l r" by (cases T) auto
    
    -- {* Finding sibling branches and their corresponding clauses: *}
    then obtain B where b_p: "internal B T \<and> branch (B@[True]) T \<and> branch (B@[False]) T"
      using internal_branch[of _ "[]" _ T] Branching_Leaf_Leaf_Tree by fastforce 
    let ?B\<^sub>1 = "B@[True]"
    let ?B\<^sub>2 = "B@[False]"

    obtain C\<^sub>1o where C\<^sub>1o_p: "C\<^sub>1o \<in> Cs \<and> falsifies\<^sub>c ?B\<^sub>1 C\<^sub>1o" using b_p clo unfolding closed_tree_def by metis 
    obtain C\<^sub>2o where C\<^sub>2o_p: "C\<^sub>2o \<in> Cs \<and> falsifies\<^sub>c ?B\<^sub>2 C\<^sub>2o" using b_p clo unfolding closed_tree_def by metis

    -- {* Standardizing the clauses apart: *}
    let ?C\<^sub>1 = "std\<^sub>1 C\<^sub>1o"
    let ?C\<^sub>2 = "std\<^sub>2 C\<^sub>2o"
    have C\<^sub>1_p: "falsifies\<^sub>c ?B\<^sub>1 ?C\<^sub>1" using std\<^sub>1_falsifies C\<^sub>1o_p by auto
    have C\<^sub>2_p: "falsifies\<^sub>c ?B\<^sub>2 ?C\<^sub>2" using std\<^sub>2_falsifies C\<^sub>2o_p by auto

    have fin: "finite ?C\<^sub>1 \<and> finite ?C\<^sub>2" using C\<^sub>1o_p C\<^sub>2o_p finite_Cs by auto

    -- {* We go down to the ground world. *}
    -- {* Finding the falsifying ground instance @{term C\<^sub>1'} of @{term ?C\<^sub>1}, and proving properties about it: *}
    
    -- {* @{term C\<^sub>1'} is falsified by @{term ?B\<^sub>1}: *}
    from C\<^sub>1_p  obtain C\<^sub>1' where C\<^sub>1'_p: "ground\<^sub>l\<^sub>s C\<^sub>1' \<and> instance_of\<^sub>l\<^sub>s C\<^sub>1' ?C\<^sub>1 \<and> falsifies\<^sub>g ?B\<^sub>1 C\<^sub>1'" by metis

    have "\<not>falsifies\<^sub>c B C\<^sub>1o" using C\<^sub>1o_p b_p clo unfolding closed_tree_def by metis
    then have "\<not>falsifies\<^sub>c B ?C\<^sub>1" using std\<^sub>1_falsifies using prod.exhaust_sel by blast
    -- {* @{term C\<^sub>1'} is not falsified by @{term B}: *}
    then have l_B: "\<not>falsifies\<^sub>g B C\<^sub>1'" using C\<^sub>1'_p by auto

    -- {* @{term C\<^sub>1'} contains a literal @{term l\<^sub>1} that is falsified by @{term ?B\<^sub>1}, but not @{term B}: *}
    from C\<^sub>1'_p l_B obtain l\<^sub>1 where l\<^sub>1_p: "l\<^sub>1 \<in> C\<^sub>1' \<and> falsifies\<^sub>l (B@[True]) l\<^sub>1 \<and> \<not>(falsifies\<^sub>l B l\<^sub>1)" by auto
    let ?i = "nat_from_fatom (get_atom l\<^sub>1)"

    -- {* @{term l\<^sub>1} is of course ground: *}
    have ground_l\<^sub>1: "ground\<^sub>l l\<^sub>1" using C\<^sub>1'_p l\<^sub>1_p by auto

    from l\<^sub>1_p have "\<not>(?i < length B \<and> B ! ?i = (\<not>sign l\<^sub>1))" using ground_l\<^sub>1 unfolding falsifies\<^sub>l_def by meson
    then have "\<not>(?i < length B \<and> (B@[True]) ! ?i = (\<not>sign l\<^sub>1))" by (metis nth_append) -- {* Not falsified by @{term B}. *}
    moreover
    from l\<^sub>1_p have "?i < length (B @ [True]) \<and> (B @ [True]) ! ?i = (\<not>sign l\<^sub>1)" unfolding falsifies\<^sub>l_def by meson
    ultimately
    have l\<^sub>1_sign_no: "?i = length B \<and> (B @ [True]) ! ?i = (\<not>sign l\<^sub>1)" by auto

    -- {* @{term l\<^sub>1} is negative: *}
    from l\<^sub>1_sign_no have l\<^sub>1_sign: "sign l\<^sub>1 = False" by auto
    from l\<^sub>1_sign_no have l\<^sub>1_no: "nat_from_fatom (get_atom l\<^sub>1) = length B" by auto

    -- {* All the other literals in @{term C\<^sub>1'} must be falsified by B, since they are falsified by @{term ?B\<^sub>1}, but not @{term l\<^sub>1}. *}
    from C\<^sub>1'_p l\<^sub>1_no l\<^sub>1_p have B_C\<^sub>1'l\<^sub>1: "falsifies\<^sub>g B (C\<^sub>1' - {l\<^sub>1})" (* This should be a lemma *)
      using other_falsified by blast

    -- {* We do the same exercise for @{term ?C\<^sub>2}, @{term C\<^sub>2'}, @{term ?B\<^sub>2}, @{term l\<^sub>2}: *}
    from C\<^sub>2_p obtain C\<^sub>2' where C\<^sub>2'_p: "ground\<^sub>l\<^sub>s C\<^sub>2' \<and> instance_of\<^sub>l\<^sub>s C\<^sub>2' ?C\<^sub>2 \<and> falsifies\<^sub>g ?B\<^sub>2 C\<^sub>2'" by metis

    have "\<not>falsifies\<^sub>c B C\<^sub>2o" using C\<^sub>2o_p b_p clo unfolding closed_tree_def by metis
    then have "\<not>falsifies\<^sub>c B ?C\<^sub>2" using std\<^sub>2_falsifies using prod.exhaust_sel by blast
    then have l_B: "\<not>falsifies\<^sub>g B C\<^sub>2'" using C\<^sub>2'_p by auto (* I already had something called l_B... I could give it a new name *)
    
    -- {* @{term C\<^sub>2'} contains a literal @{term l\<^sub>2} that is falsified by @{term ?B\<^sub>2}, but not B: *}
    from C\<^sub>2'_p l_B obtain l\<^sub>2 where l\<^sub>2_p: "l\<^sub>2 \<in> C\<^sub>2' \<and> falsifies\<^sub>l (B@[False]) l\<^sub>2 \<and> \<not>falsifies\<^sub>l B l\<^sub>2" by auto
    let ?i = "nat_from_fatom (get_atom l\<^sub>2)"

    have ground_l\<^sub>2: "ground\<^sub>l l\<^sub>2" using C\<^sub>2'_p l\<^sub>2_p by auto

    from l\<^sub>2_p have "\<not>(?i < length B \<and> B ! ?i = (\<not>sign l\<^sub>2))" using ground_l\<^sub>2 unfolding falsifies\<^sub>l_def by meson
    then have "\<not>(?i < length B \<and> (B@[False]) ! ?i = (\<not>sign l\<^sub>2))" by (metis nth_append) -- {* Not falsified by @{term B}. *}
    moreover
    from l\<^sub>2_p have "?i < length (B @ [False]) \<and> (B @ [False]) ! ?i = (\<not>sign l\<^sub>2)" unfolding falsifies\<^sub>l_def by meson
    ultimately
    have l\<^sub>2_sign_no: "?i = length B \<and> (B @ [False]) ! ?i = (\<not>sign l\<^sub>2)" by auto

    -- {* @{term l\<^sub>2} is negative: *}
    from l\<^sub>2_sign_no have l\<^sub>2_sign: "sign l\<^sub>2 = True" by auto
    from l\<^sub>2_sign_no have l\<^sub>2_no: "nat_from_fatom (get_atom l\<^sub>2) = length B" by auto

    -- {* All the other literals in @{term C\<^sub>2'} must be falsified by B, since they are falsified by 
          @{term ?B\<^sub>2}, but not @{term l\<^sub>2}. *}
    from C\<^sub>2'_p l\<^sub>2_no l\<^sub>2_p have B_C\<^sub>2'l\<^sub>2: "falsifies\<^sub>g B (C\<^sub>2' - {l\<^sub>2})"
      using other_falsified by blast

    -- {* Proving some properties about @{term C\<^sub>1'} and @{term C\<^sub>2'}, @{term l\<^sub>1} and @{term l\<^sub>2}, as well as 
          the resolvent of @{term C\<^sub>1'} and @{term C\<^sub>2'}: *}
    have l\<^sub>2cisl\<^sub>1: "l\<^sub>2\<^sup>c = l\<^sub>1" (* Could perhaps be a lemma *)
      proof -
        from l\<^sub>1_no l\<^sub>2_no ground_l\<^sub>1 ground_l\<^sub>2 have "get_atom l\<^sub>1 = get_atom l\<^sub>2"
              using nat_from_fatom_bij ground\<^sub>l_ground_fatom 
              unfolding bij_betw_def inj_on_def by metis
        then show "l\<^sub>2\<^sup>c = l\<^sub>1" using l\<^sub>1_sign l\<^sub>2_sign using sign_comp_atom by metis 
      qed
    
    have "applicable C\<^sub>1' C\<^sub>2' {l\<^sub>1} {l\<^sub>2} Resolution.\<epsilon>" unfolding applicable_def
      using l\<^sub>1_p l\<^sub>2_p C\<^sub>1'_p ground\<^sub>l\<^sub>s_vars\<^sub>l\<^sub>s l\<^sub>2cisl\<^sub>1 empty_comp2 unfolding mgu\<^sub>l\<^sub>s_def unifier\<^sub>l\<^sub>s_def by auto
    -- {* Lifting to get a resolvent of @{term ?C\<^sub>1} and @{term ?C\<^sub>2}: *}
    then obtain L\<^sub>1 L\<^sub>2 \<tau> where L\<^sub>1L\<^sub>2\<tau>_p: "applicable ?C\<^sub>1 ?C\<^sub>2 L\<^sub>1 L\<^sub>2 \<tau>  \<and> instance_of\<^sub>l\<^sub>s (resolution C\<^sub>1' C\<^sub>2' {l\<^sub>1} {l\<^sub>2} Resolution.\<epsilon>) (resolution ?C\<^sub>1 ?C\<^sub>2 L\<^sub>1 L\<^sub>2 \<tau>)"
      using std_apart_apart C\<^sub>1'_p C\<^sub>2'_p lifting[of ?C\<^sub>1 ?C\<^sub>2 C\<^sub>1' C\<^sub>2' "{l\<^sub>1}" "{l\<^sub>2}" Resolution.\<epsilon>] fin by auto


    -- {* Defining the clause to be derived, the new clausal form and the new tree: *}
    -- {* We name the resolvent @{term C}. *}
    obtain C where C_p: "C = resolution ?C\<^sub>1 ?C\<^sub>2 L\<^sub>1 L\<^sub>2 \<tau>" by auto
    obtain CsNext where CsNext_p: "CsNext = Cs \<union> {?C\<^sub>1, ?C\<^sub>2, C}" by auto
    obtain T'' where T''_p: "T'' = delete B T" by auto 
        -- {* Here we delete the two branch children @{term ?B\<^sub>1} and @{term ?B\<^sub>2} of @{term B}. *}
    
    -- {* Our new clause is falsified by the branch @{term B} of our new tree: *}
    have "falsifies\<^sub>g B ((C\<^sub>1' - {l\<^sub>1}) \<union> (C\<^sub>2' - {l\<^sub>2}))" using B_C\<^sub>1'l\<^sub>1 B_C\<^sub>2'l\<^sub>2 by cases auto
    then have "falsifies\<^sub>g B (resolution C\<^sub>1' C\<^sub>2' {l\<^sub>1} {l\<^sub>2} Resolution.\<epsilon>)" unfolding resolution_def empty_subls by auto
    then have falsifies_C: "falsifies\<^sub>c B C" using C_p L\<^sub>1L\<^sub>2\<tau>_p by auto

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
            then show "closed_branch b T'' CsNext" using clo br T''_p CsNext_p unfolding closed_tree_def by auto
          qed
      qed
    then have T''_bran2: "anybranch T'' (\<lambda>b. falsifies\<^sub>c\<^sub>s b CsNext)" by auto (* replace T''_bran with this maybe? *)

    -- {* We cut the tree even smaller to ensure only the branches are falsified, i.e. it is a closed tree: *}
    obtain T' where T'_p: "T' = cutoff (\<lambda>G. falsifies\<^sub>c\<^sub>s G CsNext) [] T''" by auto
    have T'_smaller: "treesize T' < treesize T" using treesize_cutoff[of "\<lambda>G. falsifies\<^sub>c\<^sub>s G CsNext" "[]" T''] T''_smaller unfolding T'_p by auto

    from T''_bran2 have "anybranch T' (\<lambda>b. falsifies\<^sub>c\<^sub>s b CsNext)" using cutoff_branch[of T'' "\<lambda>b. falsifies\<^sub>c\<^sub>s b CsNext"] T'_p by auto
    then have T'_bran: "anybranch T' (\<lambda>b. closed_branch b T' CsNext)" by auto
    have T'_intr: "anyinternal T' (\<lambda>p. \<not>falsifies\<^sub>c\<^sub>s p CsNext)" using T'_p cutoff_internal[of T'' "\<lambda>b. falsifies\<^sub>c\<^sub>s b CsNext"] T''_bran2 by blast
    have T'_closed: "closed_tree T' CsNext" using T'_bran T'_intr unfolding closed_tree_def by auto
    have finite_CsNext: "\<forall>C\<in>CsNext. finite C" unfolding CsNext_p C_p resolution_def using finite_Cs fin by auto

    -- {* By induction hypothesis we get a resolution derivation of @{term "{}"} from our new clausal form: *}
    from T'_smaller T'_closed have "\<exists>Cs''. resolution_deriv CsNext Cs'' \<and> {} \<in> Cs''" using ih[of T' CsNext] finite_CsNext by blast
    then obtain Cs'' where Cs''_p: "resolution_deriv CsNext Cs'' \<and> {} \<in> Cs''" by auto
    moreover
    { -- {* Proving that we can actually derive the new clausal form: *}
      have "resolution_step Cs (Cs \<union> {?C\<^sub>1})" using std\<^sub>1_renames standardize_apart C\<^sub>1o_p by (metis Un_insert_right)
      moreover
      have "resolution_step (Cs \<union> {?C\<^sub>1}) (Cs \<union> {?C\<^sub>1} \<union> {?C\<^sub>2})" using std\<^sub>2_renames[of C\<^sub>2o] standardize_apart[of C\<^sub>2o _ ?C\<^sub>2] C\<^sub>2o_p by auto 
      then have "resolution_step (Cs \<union> {?C\<^sub>1}) (Cs \<union> {?C\<^sub>1,?C\<^sub>2})" by (simp add: insert_commute)
      moreover
      then have "resolution_step (Cs \<union> {?C\<^sub>1,?C\<^sub>2}) (Cs \<union> {?C\<^sub>1,?C\<^sub>2} \<union> {C})" 
        using L\<^sub>1L\<^sub>2\<tau>_p resolution_rule[of ?C\<^sub>1 "Cs \<union> {?C\<^sub>1,?C\<^sub>2}" ?C\<^sub>2 L\<^sub>1 L\<^sub>2 \<tau> ] using C_p by auto
      then have "resolution_step (Cs \<union> {?C\<^sub>1,?C\<^sub>2}) CsNext" using CsNext_p by (simp add:  Un_commute)
      ultimately
      have "resolution_deriv Cs CsNext"  unfolding resolution_deriv_def by auto
    }
    -- {* Combining the two derivations, we get the desired derivation from @{term Cs} of @{term "{}"}: *}
    ultimately have "resolution_deriv Cs Cs''"  unfolding resolution_deriv_def by auto
    then have "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'" using Cs''_p by auto
  }
  ultimately show "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'" by auto
qed

theorem completeness:
  assumes finite_cs: "finite Cs" "\<forall>C\<in>Cs. finite C"
  assumes unsat: "\<forall>(F::hterm fun_denot) (G::hterm pred_denot) . \<not>eval\<^sub>c\<^sub>s F G Cs"
  shows "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'"
proof -
  from unsat have "\<forall>(G::hterm pred_denot) . \<not>eval\<^sub>c\<^sub>s HFun G Cs" by auto
  then obtain T where "closed_tree T Cs" using herbrand assms by blast
  then show "\<exists>Cs'. resolution_deriv Cs Cs' \<and> {} \<in> Cs'" using completeness' assms by auto
qed 

end -- {* unification locale *}

end
