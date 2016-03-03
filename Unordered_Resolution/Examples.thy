theory Examples imports Resolution begin

value "Var ''x''"
value "Fun ''one'' []"
value "Fun ''mul'' [Var ''y'',Var ''y'']"
value "Fun ''add'' [Fun ''mul'' [Var ''y'',Var ''y''], Fun ''one'' []]"

value "Pos ''greater'' [Var ''x'', Var ''y'']"
value "Neg ''less'' [Var ''x'', Var ''y'']"
value "Pos ''less'' [Var ''x'', Var ''y'']"
value "Pos ''equals''
        [Fun ''add''[Fun ''mul''[Var ''y'',Var ''y''], Fun ''one''[]],Var ''x'']"

fun F\<^sub>n\<^sub>a\<^sub>t :: "nat fun_denot" where
  " F\<^sub>n\<^sub>a\<^sub>t f [n,m] = 
     (if f = ''add'' then n + m else 
      if f = ''mul'' then n * m else 0)"
| " F\<^sub>n\<^sub>a\<^sub>t f [] = 
     (if f = ''one''  then 1 else
      if f = ''zero'' then 0 else 0)"
| " F\<^sub>n\<^sub>a\<^sub>t f us = 0"

fun G\<^sub>n\<^sub>a\<^sub>t :: "nat pred_denot" where
  "G\<^sub>n\<^sub>a\<^sub>t p [x,y] =
     (if p = ''less'' \<and> x < y then True else
      if p = ''greater'' \<and> x > y then True else 
      if p = ''equals'' \<and> x = y then True else False)"
| "G\<^sub>n\<^sub>a\<^sub>t p us = False"

fun E\<^sub>n\<^sub>a\<^sub>t :: "nat var_denot" where
  "E\<^sub>n\<^sub>a\<^sub>t x =
     (if x = ''x'' then 26 else
      if x = ''y'' then 5 else 0)"

lemma "evalt E\<^sub>n\<^sub>a\<^sub>t F\<^sub>n\<^sub>a\<^sub>t (Var ''x'') = 26" 
  by auto
lemma "evalt E\<^sub>n\<^sub>a\<^sub>t F\<^sub>n\<^sub>a\<^sub>t (Fun ''one'' []) = 1" 
  by auto
lemma "evalt E\<^sub>n\<^sub>a\<^sub>t F\<^sub>n\<^sub>a\<^sub>t (Fun ''mul'' [Var ''y'',Var ''y'']) = 25" 
  by auto
lemma 
  "evalt E\<^sub>n\<^sub>a\<^sub>t F\<^sub>n\<^sub>a\<^sub>t (Fun ''add'' [Fun ''mul'' [Var ''y'',Var ''y''], Fun ''one'' []]) = 26" 
  by auto

lemma "evall E\<^sub>n\<^sub>a\<^sub>t F\<^sub>n\<^sub>a\<^sub>t G\<^sub>n\<^sub>a\<^sub>t (Pos ''greater'' [Var ''x'', Var ''y'']) = True" 
  by auto
lemma "evall E\<^sub>n\<^sub>a\<^sub>t F\<^sub>n\<^sub>a\<^sub>t G\<^sub>n\<^sub>a\<^sub>t (Neg ''less'' [Var ''x'', Var ''y'']) = True" 
  by auto
lemma "evall E\<^sub>n\<^sub>a\<^sub>t F\<^sub>n\<^sub>a\<^sub>t G\<^sub>n\<^sub>a\<^sub>t (Pos ''less'' [Var ''x'', Var ''y'']) = False" 
  by auto
lemma "evall E\<^sub>n\<^sub>a\<^sub>t F\<^sub>n\<^sub>a\<^sub>t G\<^sub>n\<^sub>a\<^sub>t 
       (Pos ''equals'' 
         [Fun ''add'' [Fun ''mul'' [Var ''y'',Var ''y''],Fun ''one'' []]
         ,Var ''x'']
       ) = True" 
  by auto
(* value "diag 0" value "diag 1" value "diag 2" value "diag 3" value "diag 4" value "diag_hatom 0" value "undiag_hatom (diag_hatom 0)" value "diag_hatom (undiag_hatom (diag_hatom 0))" value "undiag_hatom (diag_hatom 1)" value "undiag_hatom (diag_hatom 2)" value "diag_hatom 2" value "diag_hatom 3" value "diag_hatom 4" value "diag_hatom 5" value "diag_hatom 90"  *)

definition PP :: "fterm literal" where
  "PP = Pos ''P'' [Fun ''c'' []]"

definition PQ :: "fterm literal" where
  "PQ = Pos ''Q'' [Fun ''d'' []]"

definition NP :: "fterm literal" where
  "NP = Neg ''P'' [Fun ''c'' []]"

definition NQ :: "fterm literal" where
  "NQ = Neg ''Q'' [Fun ''d'' []]"

theorem empty_mgu: "unifierls \<epsilon> L \<Longrightarrow> mguls \<epsilon> L"
unfolding unifierls_def mguls_def apply auto
apply (rule_tac x=u in exI)
using empty_comp1 empty_comp2 apply (auto)
done

theorem unifier_single: "unifierls \<sigma> {l}" 
unfolding unifierls_def by auto

theorem resolution_rule':
      "C\<^sub>1 \<in> Cs \<Longrightarrow> C\<^sub>2 \<in> Cs \<Longrightarrow> applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> 
   \<Longrightarrow> C = {resolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>} 
   \<Longrightarrow> resolution_step Cs (Cs \<union> C)"
  using resolution_rule by auto

lemma resolution_example1: 
   "resolution_deriv {{NP,PQ},{NQ},{PP,PQ}} 
                              {{NP,PQ},{NQ},{PP,PQ},{NP},{PP},{}}"
proof -
  have "resolution_step 
          {{NP,PQ},{NQ},{PP,PQ}}
         ({{NP,PQ},{NQ},{PP,PQ}} \<union> {{NP}})"
    apply (rule resolution_rule'[of "{NP,PQ}" _ "{NQ}" "{PQ}" "{NQ}" \<epsilon>])
    unfolding applicable_def varsls_def  varsl_def 
              NQ_def NP_def PQ_def PP_def resolution_def
    using unifier_single empty_mgu using empty_subls by auto 
  then have "resolution_step 
          {{NP,PQ},{NQ},{PP,PQ}}
         ({{NP,PQ},{NQ},{PP,PQ},{NP}})" 
    by (simp add: insert_commute) 
  moreover
  have "resolution_step
         {{NP,PQ},{NQ},{PP,PQ},{NP}}
        ({{NP,PQ},{NQ},{PP,PQ},{NP}} \<union> {{PP}})"
    apply (rule resolution_rule'[of "{NQ}" _ "{PP,PQ}" "{NQ}" "{PQ}" \<epsilon>])
    unfolding applicable_def varsls_def  varsl_def 
              NQ_def NP_def PQ_def PP_def resolution_def
    using unifier_single empty_mgu empty_subls apply auto
    done
  then have "resolution_step
         {{NP,PQ},{NQ},{PP,PQ},{NP}}
        ({{NP,PQ},{NQ},{PP,PQ},{NP},{PP}})" 
    by (simp add: insert_commute)
  moreover
  have "resolution_step
         {{NP,PQ},{NQ},{PP,PQ},{NP},{PP}}
        ({{NP,PQ},{NQ},{PP,PQ},{NP},{PP}} \<union> {{}})"
    apply (rule resolution_rule'[of "{NP}" _ "{PP}" "{NP}" "{PP}" \<epsilon>])
    unfolding applicable_def varsls_def  varsl_def 
              NQ_def NP_def PQ_def PP_def resolution_def
    using unifier_single empty_mgu apply (auto)
    done
  then have "resolution_step
         {{NP,PQ},{NQ},{PP,PQ},{NP},{PP}}
        ({{NP,PQ},{NQ},{PP,PQ},{NP},{PP},{}})" 
    by (simp add: insert_commute)
  ultimately
  have "resolution_deriv {{NP,PQ},{NQ},{PP,PQ}} 
                         {{NP,PQ},{NQ},{PP,PQ},{NP},{PP},{}}"
    unfolding resolution_deriv_def by auto 
  then show ?thesis by auto
qed

definition Pa :: "fterm literal" where
  "Pa = Pos ''a'' []"

definition Na :: "fterm literal" where
  "Na = Neg ''a'' []"

definition Pb :: "fterm literal" where
  "Pb = Pos ''b'' []"

definition Nb :: "fterm literal" where
  "Nb = Neg ''b'' []"

definition Paa :: "fterm literal" where
  "Paa = Pos ''a'' [Fun ''a'' []]"

definition Naa :: "fterm literal" where
  "Naa = Neg ''a'' [Fun ''a'' []]"

definition Pax :: "fterm literal" where
  "Pax = Pos ''a'' [Var ''x'']"

definition Nax :: "fterm literal" where
  "Nax = Neg ''a'' [Var ''x'']"

definition mguPaaPax :: substitution where
  "mguPaaPax = (\<lambda>x. if x = ''x'' then Fun ''a'' [] else Var x)"

lemma mguPaaPax_mgu: "mguls mguPaaPax {Paa,Pax}"
proof -
  let ?\<sigma> = "\<lambda>x. if x = ''x'' then Fun ''a'' [] else Var x"
  have a: "unifierls (\<lambda>x. if x = ''x'' then Fun ''a'' [] else Var x) {Paa,Pax}" unfolding Paa_def Pax_def unifierls_def by auto
  have b: "\<forall>u. unifierls u {Paa,Pax} \<longrightarrow> (\<exists>i. u = ?\<sigma> \<cdot> i)"
    proof (rule;rule)
      fix u
      assume "unifierls u {Paa,Pax}"
      then have uuu: "u ''x'' = Fun ''a'' []" unfolding unifierls_def Paa_def Pax_def by auto
      have "?\<sigma> \<cdot> u = u"
        proof
          fix x
          {
            assume "x=''x''"
            moreover
            have "(?\<sigma> \<cdot> u) ''x'' =  Fun ''a'' []" unfolding composition_def by auto
            ultimately have "(?\<sigma> \<cdot> u) x = u x" using uuu by auto
          }
          moreover
          {
            assume "x\<noteq>''x''"
            then have "(?\<sigma> \<cdot> u) x = (\<epsilon> x) {u}\<^sub>t" unfolding composition_def by auto
            then have "(?\<sigma> \<cdot> u) x = u x" by auto
          }
          ultimately show "(?\<sigma> \<cdot> u) x = u x" by auto
        qed
      then have "(\<exists>i. ?\<sigma> \<cdot> i = u)" by auto
      then show "(\<exists>i. u = ?\<sigma> \<cdot> i)" by auto
     qed
   from a b show ?thesis unfolding mguls_def unfolding mguPaaPax_def by auto
qed

lemma resolution_example2: 
   "resolution_deriv {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa}}
                              {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb},{Na},{}}"
proof -
  have "resolution_step 
          {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa}}
         ({{Nb,Na},{Pax},{Pa},{Na,Pb,Naa}} \<union> {{Na,Pb}})"
    apply (rule resolution_rule'[of "{Pax}" _ "{Na,Pb,Naa}" "{Pax}" "{Naa}" mguPaaPax ])
    using mguPaaPax_mgu unfolding applicable_def varsls_def  varsl_def 
          Nb_def Na_def Pax_def Pa_def Pb_def Naa_def Paa_def mguPaaPax_def resolution_def
    apply auto
    apply (rule_tac x=Na in image_eqI)
    unfolding Na_def apply auto
    apply (rule_tac x=Pb in image_eqI)
    unfolding Pb_def apply auto
    done
  then have "resolution_step 
          {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa}}
         ({{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb}})" 
    by (simp add: insert_commute)
  moreover
  have "resolution_step 
          {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb}}
         ({{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb}} \<union> {{Na}})"
    apply (rule resolution_rule'[of "{Nb,Na}" _ "{Na,Pb}" "{Nb}" "{Pb}" \<epsilon>])
    unfolding applicable_def varsls_def  varsl_def 
              Pb_def Nb_def Na_def PP_def resolution_def
    using unifier_single empty_mgu apply (auto)
    done
  then have "resolution_step 
          {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb}}
         ({{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb},{Na}})" 
    by (simp add: insert_commute)
  moreover
  have "resolution_step 
          {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb},{Na}}
         ({{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb},{Na}} \<union> {{}})"
    apply (rule resolution_rule'[of "{Na}" _ "{Pa}" "{Na}" "{Pa}" \<epsilon>])
    unfolding applicable_def varsls_def  varsl_def 
              Pa_def Nb_def Na_def PP_def resolution_def
    using unifier_single empty_mgu apply (auto)
    done
  then have "resolution_step 
          {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb},{Na}}
         ({{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb},{Na},{}})" 
    by (simp add: insert_commute)
  ultimately
  have "resolution_deriv {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa}} 
          {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa},{Na,Pb},{Na},{}}"
    unfolding resolution_deriv_def by auto 
  then show ?thesis by auto
qed

lemma ref_sound: 
  assumes deriv: "resolution_deriv Cs Cs' \<and> {} \<in> Cs'"
  shows "\<not>evalcs F G Cs"
proof -
  from deriv have "evalcs F G Cs \<Longrightarrow> evalcs F G Cs'" using lsound_derivation by auto
  moreover
  from deriv have "evalcs F G Cs' \<Longrightarrow> evalc F G {}" unfolding evalcs_def by auto
  moreover
  then have "evalc F G {} \<Longrightarrow> False" unfolding evalc_def by auto
  ultimately show ?thesis by auto
qed

lemma resolution_example1_sem: "\<not>evalcs F G {{NP, PQ}, {NQ}, {PP, PQ}}"
  using resolution_example1 ref_sound by auto

lemma resolution_example2_sem: "\<not>evalcs F G {{Nb,Na},{Pax},{Pa},{Na,Pb,Naa}}"
  using resolution_example2 ref_sound by auto

end
