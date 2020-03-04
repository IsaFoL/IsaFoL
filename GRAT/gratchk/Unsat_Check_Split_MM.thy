section \<open>Unsat Checker\<close>
theory Unsat_Check_Split_MM
imports Impl_List_Set_Ndj Grat_Basic 
begin
\<^cancel>\<open>
  Test for flexible memory management. 
  Next id can be any free id. 

  Problem with re-using IDs:
    It's expensive to delete ids from collected RAT candidate lists.
    Probably resort to filter candidate lists afterwards.

    Currently, we use maybe-head insert to update RAT candidate lists.
    That is, if we re-use an ID, it may end up with a duplicate entry
    in candidate list!?
      RL l = [\<dots>] 

    Try: Use non-distinct list for RAT candidate lists!?

  TODO: Allow memory management on clause-db, by re-using space of deleted clauses?

  TODO: Declare max-ids in advance?

\<close>  

hide_const (open) Word.slice

text \<open>
  This theory provides a formally verified unsat certificate checker.

  The checker accepts an integer array whose prefix contains a cnf formula
    (encoded as a list of null-terminated clauses), and the suffix contains
    a certificate in the GRAT format.

\<close>
  
\<^cancel>\<open>  
subsection \<open>Input Format Specification\<close>    
    
text \<open>The \<open>unsat_input\<close> locale is an iterator over integers, overlaid with an iteration
  scheme over items.\<close>
  
locale unsat_input = input it_invar' for it_invar'::"'it::linorder \<Rightarrow> _" +
  fixes  
    WFitem :: "('it \<times> 'it) set" and
    item_is_last :: "'it \<Rightarrow> bool" and
    item_next :: "'it \<rightharpoonup> 'it"
  assumes
        wf_WFitem[simp, intro!]: "wf WFitem" 
    and invar_next: 
      "\<lbrakk>it_invar it; \<not>item_is_last it; item_next it = Some it' \<rbrakk> 
        \<Longrightarrow> it_invar it'" 
    and wf_next: 
      "\<lbrakk>it_invar it; \<not>item_is_last it; item_next it = Some it' \<rbrakk> 
        \<Longrightarrow> (it',it)\<in>WFitem"
    
begin  
  lemma wf_WFitem_trancl[simp, intro!]: "wf (WFitem\<^sup>+)" 
    using wf_trancl[OF wf_WFitem] .
      
end  
\<close>   
  
  
subsection \<open>Abstract level\<close>
  

definition mkp_raw_err :: "_ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> (nat\<times>'prf) error" where
  "mkp_raw_err msg I p \<equiv> (msg, I, p)"
  
locale unsat_input = input it_invar' for it_invar'::"'it::linorder \<Rightarrow> _" +
  fixes prf_next :: "'prf \<Rightarrow> int \<times> 'prf"
begin
  abbreviation mkp_err :: "_ \<Rightarrow> (nat\<times>'prf) error" 
    where "mkp_err msg \<equiv> mkp_raw_err (msg) None None"
  abbreviation mkp_errN :: "_ \<Rightarrow>_ \<Rightarrow> (nat\<times>'prf) error" 
    where "mkp_errN msg n \<equiv> mkp_raw_err (msg) (Some (int n)) None"
  abbreviation mkp_errI :: "_ \<Rightarrow>_ \<Rightarrow> (nat\<times>'prf) error" 
    where "mkp_errI msg i \<equiv> mkp_raw_err (msg) (Some i) None"
  
  abbreviation mkp_errprf :: "_ \<Rightarrow> _ \<Rightarrow> (nat\<times>'prf) error" 
    where "mkp_errprf msg prf \<equiv> mkp_raw_err (msg) None (Some prf)"
  abbreviation mkp_errNprf :: "_ \<Rightarrow> _ \<Rightarrow>_ \<Rightarrow> (nat\<times>'prf) error" 
    where "mkp_errNprf msg n prf \<equiv> mkp_raw_err (msg) (Some (int n)) (Some prf)"
  abbreviation mkp_errIprf :: "_ \<Rightarrow> _ \<Rightarrow>_ \<Rightarrow> (nat\<times>'prf) error" 
    where "mkp_errIprf msg i prf \<equiv> mkp_raw_err (msg) (Some i) (Some prf)"
  
  
  definition parse_prf :: "nat \<times> 'prf \<Rightarrow> (_,int \<times> (nat \<times> 'prf)) enres"
    where "parse_prf \<equiv> \<lambda>(fuel,prf). doE {
      CHECK (fuel > 0) (mkp_errprf STR ''Out of fuel'' (fuel,prf));
      let (x,prf) = prf_next prf;
      ERETURN (x,(fuel - 1,prf))
    }"
  
  definition "parse_id prf \<equiv> doE {
    (x,prf) \<leftarrow> parse_prf prf;
    CHECK (x>0) (mkp_errIprf STR ''Invalid id'' x prf);
    ERETURN (nat x,prf)
  }"

  definition "parse_idZ prf \<equiv> doE {
    (x,prf) \<leftarrow> parse_prf prf;
    CHECK (x\<ge>0) (mkp_errIprf STR ''Invalid idZ'' x prf);
    ERETURN (nat x,prf)
  }"
    
    
  definition "parse_type prf \<equiv> doE {
    (v,prf) \<leftarrow> parse_prf prf;
         if v=1 then ERETURN (UNIT_PROP, prf)
    else if v=2 then ERETURN (DELETION, prf)
    else if v=3 then ERETURN (RUP_LEMMA, prf)
    else if v=4 then ERETURN (RAT_LEMMA, prf)
    else if v=5 then ERETURN (CONFLICT, prf)
    else if v=6 then ERETURN (RAT_COUNTS, prf)
    else THROW (mkp_errIprf STR ''Invalid item type'' v prf)
  }"  

  definition "parse_prf_literal prf \<equiv> doE {
    (i,prf) \<leftarrow> parse_prf prf;
    CHECK (i \<noteq> 0) (mkp_errprf STR ''Expected literal but found 0'' prf);
    ERETURN (lit_\<alpha> i, prf)
  }"
    
  definition "parse_prf_literalZ prf \<equiv> doE {
    (i,prf) \<leftarrow> parse_prf prf;
    if (i=0) then ERETURN (None,prf) 
    else ERETURN (Some (lit_\<alpha> i), prf)
  }"
    
    
  abbreviation "at_end it \<equiv> it = it_end"
  abbreviation "at_Z it \<equiv> it_peek it = litZ"

  definition prfWF :: "((nat\<times>'prf) \<times> (nat\<times>'prf)) set" 
    where "prfWF \<equiv> measure fst"
  lemma wf_prfWF[simp, intro!]: "wf prfWF" unfolding prfWF_def by simp
  lemma wf_prfWFtrcl[simp, intro!]: "wf (prfWF\<^sup>+)"
    by (simp add: wf_trancl)
      
  lemma parse_prf_spec[THEN ESPEC_trans,refine_vcg]:
    "parse_prf prf \<le> ESPEC (\<lambda>_. True) (\<lambda>(_,prf'). (prf',prf)\<in>prfWF\<^sup>+)"
    unfolding parse_prf_def 
    by refine_vcg (auto simp: prfWF_def)
      
  lemma parse_id_spec[THEN ESPEC_trans,refine_vcg]: 
    "parse_id prf
        \<le> ESPEC (\<lambda>_. True) (\<lambda>(x,prf'). (prf',prf)\<in>prfWF\<^sup>+ \<and> x>0)"
    unfolding parse_id_def 
    by refine_vcg auto  

  lemma parse_idZ_spec[THEN ESPEC_trans,refine_vcg]: 
    "parse_idZ prf
        \<le> ESPEC (\<lambda>_. True) (\<lambda>(x,prf'). (prf',prf)\<in>prfWF\<^sup>+)"
    unfolding parse_idZ_def 
    by refine_vcg auto  
      
  lemma parse_type_spec[THEN ESPEC_trans,refine_vcg]: 
    "parse_type prf 
        \<le> ESPEC (\<lambda>_. True) (\<lambda>(x,prf'). (prf',prf)\<in>prfWF\<^sup>+)"
    unfolding parse_type_def 
    by refine_vcg auto  

      
  lemma parse_prf_literal_spec[THEN ESPEC_trans,refine_vcg]: 
    "parse_prf_literal prf
        \<le> ESPEC (\<lambda>_. True) (\<lambda>(_,prf'). (prf',prf)\<in>prfWF\<^sup>+)"
    unfolding parse_prf_literal_def 
    by refine_vcg auto  

  lemma parse_prf_literalZ_spec[THEN ESPEC_trans,refine_vcg]: 
    "parse_prf_literalZ prf
        \<le> ESPEC (\<lambda>_. True) (\<lambda>(_,prf'). (prf',prf)\<in>prfWF\<^sup>+)"
    unfolding parse_prf_literalZ_def 
    by refine_vcg auto  
      
end  

type_synonym clausemap = "(id \<rightharpoonup> var clause) \<times> (var literal \<rightharpoonup> id set)"
type_synonym state = "clausemap \<times> (var \<rightharpoonup> bool)"

definition "cm_invar \<equiv> \<lambda>(CM,RL). 
    (\<forall>C\<in>ran CM. \<not>is_syn_taut C)
  \<and> (\<forall>l s. RL l = Some s \<longrightarrow> s \<supseteq> {i. \<exists>C. CM i = Some C \<and> l\<in>C})"
definition "cm_F \<equiv> \<lambda>(CM,RL). ran CM"
  
definition "cm_ids \<equiv> \<lambda>(CM, RL). dom CM"

context unsat_input begin
  
\<^cancel>\<open> Map Interface \<close>
definition resolve_id :: "clausemap \<Rightarrow> id \<Rightarrow> (_,var clause) enres" 
  where "resolve_id \<equiv> \<lambda>(CM,RL) i. doE { 
    CHECK (i\<in>dom CM) (mkp_errN STR ''Invalid clause id'' i);
    ERETURN (the (CM i)) 
  }"
  
definition remove_id :: "id \<Rightarrow> clausemap \<Rightarrow> (_, clausemap) enres"
  where "remove_id \<equiv> \<lambda>i (CM,RL). ERETURN (CM(i:=None),RL)"
  
definition "remove_ids CMRL\<^sub>0 prf \<equiv> doE {
  (i,prf) \<leftarrow> parse_idZ prf;
  (CMRL,i,prf) \<leftarrow> EWHILEIT 
    (\<lambda>(CMRL,i,it).  cm_invar CMRL
                \<and> cm_F CMRL \<subseteq> cm_F CMRL\<^sub>0 
                \<and> cm_ids CMRL \<subseteq> cm_ids CMRL\<^sub>0) 
    (\<lambda>(_,i,_). i\<noteq>0) 
    (\<lambda>(CMRL,i,prf). doE {
      CMRL \<leftarrow> remove_id i CMRL;
      (i,prf) \<leftarrow> parse_idZ prf;
      ERETURN (CMRL,i,prf)
    }) (CMRL\<^sub>0,i,prf);
  ERETURN (CMRL,prf)
}"
    
    
    
definition add_clause 
  :: "id \<Rightarrow> var clause \<Rightarrow> clausemap \<Rightarrow> (_, clausemap) enres"  
  where "add_clause \<equiv> \<lambda>i C (CM,RL). doE {
    EASSERT (\<not>is_syn_taut C);
    EASSERT (i\<notin>cm_ids (CM,RL));
    let CM = CM(i \<mapsto> C);
    let RL = (\<lambda>l. case RL l of 
        None \<Rightarrow> None 
      | Some s \<Rightarrow> if l\<in>C then Some (insert i s) else Some s);
    ERETURN (CM,RL)
  }"
  
definition get_rat_candidates 
  :: "clausemap \<Rightarrow> (var \<rightharpoonup> bool) \<Rightarrow> var literal \<Rightarrow> (_,id set) enres"
  where
  "get_rat_candidates \<equiv> \<lambda>(CM,RL) A l. doE {
    let l = neg_lit l;
    CHECK (RL l \<noteq> None) (mkp_err STR ''Resolution literal not declared'');
    \<^cancel>\<open> Get collected candidates \<close>
    let cands_raw = the (RL l); 
    \<^cancel>\<open> Filter out deleted, not containing l, and being blocked \<close>
    let cands = { i\<in>cands_raw. 
                    \<exists>C. CM i = Some C 
                      \<and> l\<in>C \<and> sem_clause' (C - {l}) A \<noteq> Some True };
    ERETURN cands
  }"
  
  
lemma resolve_id_correct[THEN ESPEC_trans,refine_vcg]:
  "resolve_id CMRL i 
    \<le> ESPEC (\<lambda>_. i\<notin>dom (fst CMRL)) (\<lambda>C. C \<in> cm_F CMRL \<and> fst CMRL i = Some C)"
  unfolding resolve_id_def
  apply refine_vcg
  apply (auto simp: cm_F_def intro: ranI)
  done

lemma remove_id_correct[THEN ESPEC_trans,refine_vcg]:
  "cm_invar CMRL 
  \<Longrightarrow> remove_id i CMRL 
      \<le> ESPEC 
          (\<lambda>_. False) 
          (\<lambda>CMRL'. cm_invar CMRL' 
                \<and> cm_F CMRL' \<subseteq> cm_F CMRL 
                \<and> cm_ids CMRL' \<subseteq> cm_ids CMRL)"
  unfolding remove_id_def
  apply (refine_vcg)
  apply (auto 
          simp: cm_F_def ran_def restrict_map_def cm_invar_def cm_ids_def 
          split: if_split_asm)
  apply fastforce
  done

\<^cancel>\<open> TODO: Move to Misc \<close>
lemma rtrancl_inv_image_ss: "(inv_image R f)\<^sup>* \<subseteq> inv_image (R\<^sup>*) f"
proof (clarify)
  fix a b
  assume "(a,b) \<in> (inv_image R f)\<^sup>*"
  thus "(a,b) \<in> inv_image (R\<^sup>*) f"
    by induction auto  
qed    
    
lemmas rtrancl_inv_image_ssI = rtrancl_inv_image_ss[THEN set_mp]  
  
lemma remove_ids_correct[THEN ESPEC_trans,refine_vcg]:
  "\<lbrakk>cm_invar CMRL\<rbrakk>
  \<Longrightarrow> remove_ids CMRL prf
      \<le> ESPEC 
          (\<lambda>_. True) 
          (\<lambda>(CMRL',prf'). cm_invar CMRL' 
                \<and> cm_F CMRL' \<subseteq> cm_F CMRL 
                \<and> cm_ids CMRL' \<subseteq> cm_ids CMRL
                \<and> (prf',prf)\<in>prfWF\<^sup>+
          )"
  unfolding remove_ids_def  
  apply (refine_vcg EWHILEIT_rule[where 
          R="inv_image (prfWF\<^sup>+) (\<lambda>(_,_,prf). prf)"
          ])
  by (auto dest: rtrancl_inv_image_ssI)
    
    
lemma add_clause_correct[THEN ESPEC_trans,refine_vcg]:
  "\<lbrakk>cm_invar CM; i\<notin>cm_ids CM; \<not>is_syn_taut C\<rbrakk> \<Longrightarrow> 
    add_clause i C CM \<le> ESPEC (\<lambda>_. False) (\<lambda>CM'. 
        cm_F CM' = insert C (cm_F CM) 
      \<and> cm_invar CM' 
      \<and> cm_ids CM' = insert i (cm_ids CM)
    )"
  unfolding add_clause_def
  apply (refine_vcg)
  apply (vc_solve 
          simp: cm_ids_def cm_F_def ran_def restrict_map_def cm_invar_def 
          split: option.split 
          solve: asm_rl)
  subgoal by fastforce
  \<^cancel>\<open>subgoal by (auto; metis (no_types, hide_lams) insertCI 
                          not_Some_eq option.inject)\<close>
  done
  
definition "rat_candidates CM A reslit 
  \<equiv> {i. \<exists>C. CM i = Some C 
            \<and> neg_lit reslit \<in> C 
            \<and> \<not>is_blocked A (C-{neg_lit reslit})}"

lemma is_syn_taut_mono_aux: "is_syn_taut (C-X) \<Longrightarrow> is_syn_taut C"
  by (auto simp: is_syn_taut_def)

lemma get_rat_candidates_correct[THEN ESPEC_trans,refine_vcg]:
  "\<lbrakk> cm_invar CM \<rbrakk> 
  \<Longrightarrow> get_rat_candidates CM A reslit 
      \<le> ESPEC (\<lambda>_. True) (\<lambda>r. r=rat_candidates (fst CM) A reslit)"
  unfolding get_rat_candidates_def
  apply refine_vcg
  unfolding cm_invar_def rat_candidates_def is_blocked_def
  apply (auto dest!: is_syn_taut_mono_aux simp: ranI)
  apply force
  done
  

definition "check_unit_clause A C 
  \<equiv> ESPEC (\<lambda>_. \<not>is_unit_clause A C) (\<lambda>l. is_unit_lit A C l)"
  
definition "apply_unit i CM A \<equiv> doE {
  C \<leftarrow> resolve_id CM i;
  l \<leftarrow> check_unit_clause A C;
  EASSERT (sem_lit' l A = None);
  ERETURN (assign_lit A l)
}"
  

  
definition "apply_units CM A prf \<equiv> doE {
  (i,prf) \<leftarrow> parse_idZ prf;
  (A,i,prf) \<leftarrow> EWHILET 
    (\<lambda>(A,i,prf). i\<noteq>0) 
    (\<lambda>(A,i,prf). doE {
      A \<leftarrow> apply_unit i CM A;
      (i,prf) \<leftarrow> parse_idZ prf;
      ERETURN (A,i,prf)
    }) (A,i,prf);
  ERETURN (A,prf)
}"

lemma apply_unit_correct[THEN ESPEC_trans, refine_vcg]: 
  "apply_unit i CM A \<le> ESPEC (\<lambda>_. True) (\<lambda>A'. equiv' (cm_F CM) A A')"
  unfolding apply_unit_def check_unit_clause_def
  apply (refine_vcg)
  apply (auto simp: unit_propagation)
  apply (auto simp: is_unit_lit_def)
  done

lemma apply_units_correct[THEN ESPEC_trans, refine_vcg]:
  "apply_units CM A prf 
        \<le> ESPEC 
            (\<lambda>_. True) 
            (\<lambda>(A',prf'). equiv' (cm_F CM) A A' \<and> (prf',prf)\<in>prfWF\<^sup>+)"
  unfolding apply_units_def
  apply (refine_vcg 
      EWHILET_rule[where 
            I="\<lambda>(A',_,_). equiv' (cm_F CM) A A'" 
        and R="inv_image (prfWF\<^sup>+) (\<lambda>(_,_,prf). prf)"
      ]
      )
  apply (auto dest: equiv'_trans rtrancl_inv_image_ssI)
  done

text \<open>Parse a clause and check that it is not blocked. \<close>
definition "parse_check_blocked A it \<equiv> doE {EASSERT (it_invar it); ESPEC 
  (\<lambda>_. True) 
  (\<lambda>(C,A',it'). (\<exists>l. 
        lz_string litZ it l it' 
      \<and> it_invar it' 
      \<and> C=clause_\<alpha> l 
      \<and> \<not>is_blocked A C 
      \<and> A' = and_not_C A C))}" 

\<^cancel>\<open>abbreviation "pebERR \<equiv> (STR ''Parsed beyond end'',None,None)::'it error"\<close>
  
definition parse_skip_listZ :: "(nat\<times>'prf) \<Rightarrow> (_,nat\<times>'prf) enres" where
  "parse_skip_listZ prf \<equiv> doE {
    (x,prf) \<leftarrow> parse_prf prf;
    (_,prf) \<leftarrow> EWHILET (\<lambda>(x,prf). x\<noteq>0) (\<lambda>(x,prf). parse_prf prf) (x,prf);
    ERETURN prf
  }"

lemma parse_skip_listZ_correct[THEN ESPEC_trans, refine_vcg]: 
  shows "parse_skip_listZ prf
          \<le> ESPEC (\<lambda>_. True) (\<lambda>prf'. (prf',prf)\<in>prfWF\<^sup>+)"
  unfolding parse_skip_listZ_def
  apply (refine_vcg EWHILET_rule[where R="inv_image (prfWF\<^sup>+) snd" and I="\<lambda>_. True"])
  apply (auto dest: rtrancl_inv_image_ssI) 
  done
  
 
text \<open>Too keep proofs more readable, we extract the logic used to check
  that a RAT-proof provides an exhaustive list of the expected candidates.\<close>

definition "check_candidates candidates prf check \<equiv> doE {
  (cand,prf) \<leftarrow> parse_idZ prf;
  (candidates,cand,prf) \<leftarrow> EWHILET
    (\<lambda>(_,cand,_). cand\<noteq>0)
    (\<lambda>(candidates,cand,prf). doE {
      if cand \<in> candidates then doE {
        let candidates = candidates - {cand};
        prf \<leftarrow> check cand prf;
        (cand,prf) \<leftarrow> parse_idZ prf;
        ERETURN (candidates,cand,prf)
      } else doE {
        prf \<leftarrow> parse_skip_listZ prf; \<^cancel>\<open> Skip over unit propagation \<close>
        (_,prf) \<leftarrow> parse_prf prf; \<^cancel>\<open> Skip over conflict clause \<close>
        (cand,prf) \<leftarrow> parse_idZ prf;
        ERETURN (candidates,cand,prf)
      }
    }) (candidates,cand,prf);

  CHECK (candidates = {}) (mkp_errprf STR ''Too few RAT-candidates in proof'' prf);
  ERETURN prf
}"

lemma check_candidates_rule[THEN ESPEC_trans, zero_var_indexes]: 
  assumes check_correct: "\<And>cand prf. 
    \<lbrakk> cand\<in>candidates \<rbrakk> 
      \<Longrightarrow> check cand prf
          \<le> ESPEC (\<lambda>_. True) (\<lambda>prf'. \<Phi> cand \<and> (prf',prf)\<in>prfWF\<^sup>+)"
  shows "check_candidates candidates prf check 
          \<le> ESPEC 
              (\<lambda>_. True) 
              (\<lambda>prf'. (\<forall>cand\<in>candidates. \<Phi> cand) \<and> (prf',prf)\<in>prfWF\<^sup>+)"
  supply check_correct[THEN ESPEC_trans, refine_vcg]  
  unfolding check_candidates_def
  apply (refine_vcg 
      EWHILET_rule[where 
        I="\<lambda>(cleft,cand,prf). 
          cleft \<subseteq> candidates
        \<and> (\<forall>c\<in>candidates - cleft. \<Phi> c)"
      and R="inv_image (prfWF\<^sup>+) (\<lambda>(_,_,prf). prf)"
      ])
  by (auto dest: rtrancl_inv_image_ssI)

\<^cancel>\<open> id id* 0 id, advance iterator by one clause \<close>
definition check_rup_proof :: "state \<Rightarrow> 'it \<Rightarrow> (nat\<times>'prf) \<Rightarrow> (_, state \<times> 'it \<times> (nat\<times>'prf)) enres" where
  "check_rup_proof \<equiv> \<lambda>(CM,A\<^sub>0) it prf. doE {
    (i,prf) \<leftarrow> parse_id prf;
    CHECK (i\<notin>cm_ids CM) (mkp_errNprf STR ''Duplicate ID'' i prf);
    (C,A',it) \<leftarrow> parse_check_blocked A\<^sub>0 it;
    (A',prf) \<leftarrow> apply_units CM A' prf;
    (confl_id,prf) \<leftarrow> parse_id prf;
    confl \<leftarrow> resolve_id CM confl_id;
    CHECK (is_conflict_clause A' confl)
          (mkp_errNprf STR ''Expected conflict clause'' confl_id prf);
    EASSERT (redundant_clause (cm_F CM) A\<^sub>0 C);
    EASSERT (i \<notin> cm_ids CM);
    CM \<leftarrow> add_clause i C CM;
    ERETURN ((CM,A\<^sub>0),it,prf)
  }"
 
lemma check_rup_proof_correct[THEN ESPEC_trans, refine_vcg]: 
  assumes [simp]: "s=(CM,A)"
  assumes "cm_invar CM"
  assumes "it_invar it"
  shows
  "check_rup_proof s it prf \<le> ESPEC (\<lambda>_. True) (\<lambda>((CM',A'),it',prf'). 
      cm_invar CM'
    \<and> (sat' (cm_F CM) A \<longrightarrow> sat' (cm_F CM') A')
    \<and> (it_invar it') \<and> (prf',prf)\<in>prfWF\<^sup>+
  )"  
  unfolding check_rup_proof_def parse_check_blocked_def 
  apply refine_vcg
  using assms
  by (vc_solve 
      simp: 
      split!: if_split_asm 
      intro: implied_is_redundant one_step_implied syn_taut_imp_blocked 
      solve: asm_rl)
  

\<^cancel>\<open> lit id lit* 0 id* 0 (id id* 0 id)* 0 \<close>
definition check_rat_proof :: "state \<Rightarrow> 'it \<Rightarrow> (nat \<times> 'prf) \<Rightarrow> (_, state \<times> 'it \<times> (nat \<times> 'prf)) enres" where
  "check_rat_proof \<equiv> \<lambda>(CM,A\<^sub>0) it prf. doE {
    (reslit,prf) \<leftarrow> parse_prf_literal prf;

    CHECK (sem_lit' reslit A\<^sub>0 \<noteq> Some False) 
          (mkp_errprf STR ''Resolution literal is false'' prf);
    (i,prf) \<leftarrow> parse_id prf;
    CHECK (i\<notin>cm_ids CM) (mkp_errNprf STR ''Duplicate ID'' i prf);
    \<^cancel>\<open>(C,it) \<leftarrow> lift_parser parse_clause it;\<close>
    (C,A',it) \<leftarrow> parse_check_blocked A\<^sub>0 it;
    CHECK (reslit \<in> C) (mkp_errprf STR ''Resolution literal not in clause'' prf);
    (A',prf) \<leftarrow> apply_units CM A' prf;
    candidates \<leftarrow> get_rat_candidates CM A' reslit;
    prf \<leftarrow> check_candidates candidates prf (\<lambda>cand_id prf. doE {
      cand \<leftarrow> resolve_id CM cand_id;

      EASSERT (\<not>is_blocked A' (cand-{neg_lit reslit}));
      let A'' = and_not_C A' (cand-{neg_lit reslit});
      (A'',prf) \<leftarrow> apply_units CM A'' prf;
      (confl_id,prf) \<leftarrow> parse_id prf;
      confl \<leftarrow> resolve_id CM confl_id;
      CHECK (is_conflict_clause A'' confl) 
            (mkp_errprf STR ''Expected conflict clause'' prf);
      EASSERT (implied_clause (cm_F CM) A\<^sub>0 (C \<union> (cand-{neg_lit reslit})));
      ERETURN prf
    });

    EASSERT (redundant_clause (cm_F CM) A\<^sub>0 C);
    EASSERT (i \<notin> cm_ids CM);
    CM \<leftarrow> add_clause i C CM;
    ERETURN ((CM,A\<^sub>0),it,prf)
  }"

  
  
lemma rat_criterion:
  assumes LIC: "reslit\<in>C"
  assumes NFALSE: "sem_lit' reslit A \<noteq> Some False"
  assumes EQ1: "equiv' (cm_F (CM, RL)) (and_not_C A C) A'"    
  assumes CANDS: "\<forall>cand\<in>rat_candidates CM A' reslit. 
                    implied_clause 
                      (cm_F (CM,RL)) 
                      A 
                      (C \<union> ((the (CM cand)) - {neg_lit reslit}))"  
  shows "redundant_clause (cm_F (CM,RL)) A C"
proof (rule abs_rat_criterion[OF LIC NFALSE]; safe)
  fix D
  assume A: "D\<in>cm_F (CM,RL)" "neg_lit reslit \<in> D"
  
  show "implied_clause (cm_F (CM, RL)) A (C \<union> (D - {neg_lit reslit}))"
  proof (cases "is_blocked A' (D - {neg_lit reslit})")
    case False 
    with A obtain cand 
      where "D=the (CM cand)" and "cand\<in>rat_candidates CM A' reslit"
      by (force simp: rat_candidates_def cm_F_def ran_def)
    thus ?thesis
      using CANDS by auto
  next
    case True
    thus ?thesis
      apply (rule_tac two_step_implied)
      using EQ1 by auto
  qed
qed  
    

lemma check_rat_proof_correct[THEN ESPEC_trans, refine_vcg]: 
  assumes [simp]: "s=(CM,A)"
  assumes "cm_invar CM"
  assumes "it_invar it"
  shows
  "check_rat_proof s it prf \<le> ESPEC (\<lambda>_. True) (\<lambda>((CM',A'),it',prf'). 
      cm_invar CM'
    \<and> (sat' (cm_F CM) A \<longrightarrow> sat' (cm_F CM') A')
    \<and> it_invar it' \<and> (prf',prf)\<in>prfWF\<^sup>+
  )"  
  unfolding check_rat_proof_def parse_check_blocked_def 
  apply refine_vcg
  subgoal using assms by auto  
  subgoal using assms by auto  
  using assms    
  apply (cases CM)    
  apply (elim conjE exE; simp; elim conjE)
  apply hypsubst apply simp
  subgoal premises prems for reslit prf1 i prf2 it' A' prf3 CM RL l
  proof -  
    from prems have A:
           "reslit \<in> clause_\<alpha> l"
       and CMI: "cm_invar (CM, RL)" 
       and RESLIT_SEM: "sem_lit' (reslit) A \<noteq> Some False"
       and INID: "i\<notin>cm_ids (CM, RL)"
       and NBLK: "\<not> is_blocked A (clause_\<alpha> l)"
       and EQ1: "equiv' (cm_F (CM, RL)) (and_not_C A (clause_\<alpha> l)) A'"    
       and [simp]: "it_invar it'"
       and PRF: "(prf1, prf) \<in> prfWF\<^sup>+" "(prf2, prf1) \<in> prfWF\<^sup>+" "(prf3, prf2) \<in> prfWF\<^sup>+"
      by - assumption+
    
    from A have ARIC: "reslit \<in> clause_\<alpha> l" by auto
        
    show ?thesis
      apply (refine_vcg check_candidates_rule[where 
              \<Phi>="\<lambda>i. implied_clause 
                        (cm_F (CM,RL)) 
                        A 
                        (clause_\<alpha> l \<union> (the (CM i) - {neg_lit reslit}))"])
      apply vc_solve
      applyS (auto simp: rat_candidates_def)
      subgoal
        thm two_step_implied
        apply (rule two_step_implied)
        apply (rule exI[where x=A'])
        using EQ1 apply auto  
        done
      applyS auto []
      subgoal
        apply (rule rat_criterion[OF ARIC RESLIT_SEM EQ1])
        apply auto
        done
      applyS (rule CMI)
      subgoal using INID by simp  
      subgoal using NBLK by (auto intro: syn_taut_imp_blocked)
      subgoal using PRF by auto
      done
  qed
  done
    

definition check_item :: "state \<Rightarrow> 'it \<Rightarrow> (nat \<times> 'prf) \<Rightarrow> (_, (state \<times> 'it \<times> (nat \<times> 'prf)) option) enres"
  where "check_item \<equiv> \<lambda>(CM,A) it prf. doE {
    (ty,prf) \<leftarrow> parse_type prf;
    case ty of
      INVALID \<Rightarrow> THROW (mkp_err STR ''Invalid item'')
    | UNIT_PROP \<Rightarrow> doE {
        (A,prf) \<leftarrow> apply_units CM A prf;
        ERETURN (Some ((CM,A),it,prf))
      }
    | DELETION \<Rightarrow> doE {
        (CM,prf) \<leftarrow> remove_ids CM prf;
        ERETURN (Some ((CM,A),it,prf))
      }
    | RUP_LEMMA \<Rightarrow> doE {
        s \<leftarrow> check_rup_proof (CM,A) it prf;
        ERETURN (Some s)
      }
    | RAT_LEMMA \<Rightarrow> doE {
        s \<leftarrow> check_rat_proof (CM,A) it prf;
        ERETURN (Some s)
      }
    | CONFLICT \<Rightarrow> doE {
        (i,prf) \<leftarrow> parse_id prf;
        C \<leftarrow> resolve_id CM i;
        CHECK (is_conflict_clause A C) 
              (mkp_errNprf STR ''Conflict clause has no conflict'' i prf);
        ERETURN None
      }
    | RAT_COUNTS \<Rightarrow> 
        THROW (mkp_errprf STR ''Not expecting rat-counts in the middle of proof'' prf)
  }"
  
lemma check_item_correct_pre: 
  assumes [simp]: "s = (CM,A)"
  assumes "cm_invar CM"  
  assumes [simp]: "it_invar it"
  shows "check_item s it prf \<le> ESPEC (\<lambda>_. True) (\<lambda>
      Some ((CM',A'),it',prf') \<Rightarrow> 
          cm_invar CM' 
        \<and> (sat' (cm_F CM) A \<longrightarrow> sat' (cm_F CM') A')
        \<and> it_invar it' \<and> (prf',prf)\<in>prfWF\<^sup>+
    | None \<Rightarrow> \<not>sat' (cm_F CM) A
  )"  
  using assms(2,3)  
  apply clarsimp
  unfolding check_item_def
  apply refine_vcg
  apply (split item_type.split; intro allI impI conjI)
  applyS (refine_vcg; auto)
  applyS (refine_vcg; auto simp: sat'_equiv)
  applyS (refine_vcg; auto simp: sat'_antimono)
  applyS (refine_vcg; auto)
  applyS (refine_vcg; auto)
  applyS (refine_vcg; auto simp: conflict_clause_imp_no_models sat'_def)
  applyS (refine_vcg; auto)
  done
  

lemma check_item_correct[THEN ESPEC_trans, refine_vcg]: 
  assumes "case s of (CM,A) \<Rightarrow> cm_invar CM"
  assumes "it_invar it"  
  shows "check_item s it prf \<le> ESPEC (\<lambda>_. True) (case s of (CM,A) \<Rightarrow> (\<lambda>
      Some ((CM',A'),it',prf') \<Rightarrow> 
          cm_invar CM' 
        \<and> (sat' (cm_F CM) A \<longrightarrow> sat' (cm_F CM') A')
        \<and> it_invar it' \<and> (prf',prf)\<in>prfWF\<^sup>+
    | None \<Rightarrow> \<not>sat' (cm_F CM) A)
  )"  
  using check_item_correct_pre[of s _ _ it "prf"] assms
  apply (cases s) by auto


definition cm_empty :: "clausemap" where "cm_empty \<equiv> (Map.empty, Map.empty)"
lemma cm_empty_invar[simp]: "cm_invar cm_empty" 
  by (auto simp: cm_empty_def cm_invar_def)
lemma cm_F_empty[simp]: "cm_F cm_empty = {}" 
  by (auto simp: cm_empty_def cm_F_def)
lemma cm_ids_empty[simp]: "cm_ids cm_empty = {}" 
  by (auto simp: cm_empty_def cm_ids_def)

lemma cm_ids_empty_imp_F_empty: "cm_ids CM = {} \<Longrightarrow> cm_F CM = {}"
  unfolding cm_F_def cm_ids_def by (auto simp: ran_def)
  
\<^cancel>\<open>    
\<^cancel>\<open> TODO: Can we remove that? \<close>    
definition read_cnf 
  :: "var clause list \<Rightarrow> clausemap \<Rightarrow> (_, clausemap \<times> nat) enres" 
  where "read_cnf L CM \<equiv> doE {
    (CM, next_id) \<leftarrow> enfoldli L (\<lambda>_. True) (\<lambda>C (CM,i). doE {
      if (is_syn_taut C) then
        ERETURN (CM,i+1)
      else doE {
        CM \<leftarrow> add_clause i C CM;
        ERETURN (CM,i+1)
      }
    }) (CM,1);
    ERETURN (CM, next_id - 1)
  }"

lemma read_cnf_correct[THEN ESPEC_trans, refine_vcg]: 
  "\<lbrakk> cm_invar CM; cm_ids CM = {} \<rbrakk> 
  \<Longrightarrow> read_cnf F CM 
      \<le> ESPEC 
          (\<lambda>_. True) 
          (\<lambda>(CM,last_id). cm_invar CM 
                        \<and> sat (cm_F CM) = sat (set F) 
                        \<and> (\<forall>i\<in>cm_ids CM. i\<le>last_id))"
  unfolding read_cnf_def
  apply (refine_vcg enfoldli_rule[where 
            I="\<lambda>l1 _ (CM,next_id). 
                  cm_invar CM 
                \<and> SAT_Basic.models (cm_F CM) = SAT_Basic.models (set l1) 
                \<and> (\<forall>i\<in>cm_ids CM. i<next_id)"])
  apply (auto simp: SAT_Basic.models_def sat_def cm_ids_empty_imp_F_empty)
  done
\<close>

definition "read_clause_check_taut itE it A \<equiv> doE {
  EASSERT (A = Map.empty);
  EASSERT (it_invar it \<and> it_invar itE \<and> itran itE it_end);
  (it',(t,A)) \<leftarrow> parse_lz 
    (mkp_err STR ''Parsed beyond end'')   
    litZ itE it (\<lambda>_. True) (\<lambda>x (t,A). doE {
      let l = lit_\<alpha> x;
      if (sem_lit' l A = Some False) then ERETURN (True,A)
      else ERETURN (t,assign_lit A l)
    }) (False,A);

  A \<leftarrow> iterate_lz litZ itE it (\<lambda>_. True) (\<lambda>x A. doE {
    let A = A(var_of_lit (lit_\<alpha> x) := None);
    ERETURN A
  }) A;

  ERETURN (it',(t,A))
}"
   
lemma clause_assignment_syn_taut_aux: 
  "\<lbrakk>\<forall>l. (sem_lit' l A = Some True) = (l \<in> C); is_syn_taut C\<rbrakk> \<Longrightarrow> False"  
  apply (clarsimp simp: is_syn_taut_conv)
  by (metis map_option_eq_Some option.inject sem_neg_lit')  
  
    
  
lemma read_clause_check_taut_correct[THEN ESPEC_trans,refine_vcg]: 
  "\<lbrakk>itran it itE; it_invar itE; A = Map.empty\<rbrakk> \<Longrightarrow> 
  read_clause_check_taut itE it A
  \<le> ESPEC 
      (\<lambda>_. True) 
      (\<lambda>(it',(t,A)). A = Map.empty 
                  \<and> (\<exists>l. lz_string litZ it l it' 
                        \<and> itran it' itE 
                        \<and> (t = is_syn_taut (clause_\<alpha> l))))"  
  unfolding read_clause_check_taut_def  
  apply (refine_vcg 
          parse_lz_rule[where 
            \<Phi>="\<lambda>lst (t,A). dom A \<subseteq> var_of_lit`clause_\<alpha> lst 
                \<and> (t \<longrightarrow> is_syn_taut (clause_\<alpha> lst))
                \<and> (\<not>t \<longrightarrow> (\<forall>l. sem_lit' l A = Some True \<longleftrightarrow> l \<in> clause_\<alpha> lst))
            "]
          iterate_lz_rule[where \<Phi>="\<lambda>_ l2 A. dom A \<subseteq> var_of_lit`clause_\<alpha> l2"]  
  )  
  apply (vc_solve simp: not_Some_bool_if itran_invarI)
  applyS auto  
  applyS (auto simp: is_syn_taut_def)
  applyS (auto simp: assign_lit_def split: if_splits)
  applyS (auto simp: is_syn_taut_def)  
  applyS (force simp: sem_lit'_assign_conv split: if_splits)
  applyS (auto)  
  applyS (auto simp: itran_ord)  
  applyS (auto)   
  applyS (auto)   
  applyS (auto dest: clause_assignment_syn_taut_aux)  
  done 
    
definition read_cnf_new 
  :: "'it \<Rightarrow> 'it \<Rightarrow> clausemap \<Rightarrow> (_, clausemap) enres"    
  where "read_cnf_new itE it CM \<equiv> doE {
    (CM,next_id,A) \<leftarrow> tok_fold itE it (\<lambda>it (CM,next_id,A). doE {
      (it',(t,A)) \<leftarrow> read_clause_check_taut itE it A;
      if t then ERETURN (it', (CM,next_id+1,A))
      else doE {
        EASSERT (\<exists>l it'. lz_string litZ it l it' \<and> it_invar it');
        let C = clause_\<alpha> (the_lz_string litZ it);
        CM \<leftarrow> add_clause next_id C CM;
        ERETURN (it',(CM,next_id+1,A))
      }
    }) (CM,1,Map.empty);
    ERETURN (CM)
  }"
    
lemma read_cnf_new_correct[THEN ESPEC_trans, refine_vcg]:
  "\<lbrakk>seg it lst itE; cm_invar CM; cm_ids CM = {}; it_invar itE\<rbrakk> 
  \<Longrightarrow> read_cnf_new itE it CM 
  \<le> ESPEC (\<lambda>_. True) (\<lambda>(CM). 
        (lst \<noteq> [] \<longrightarrow> last lst = litZ)
      \<and> cm_invar CM 
      \<and> sat (cm_F CM) = sat (set (map clause_\<alpha> (tokenize litZ lst))) 
  )"    
  unfolding read_cnf_new_def    
  apply (refine_vcg tok_fold_rule[where 
        \<Phi>="\<lambda>lst (CM,next_id,A). 
            A = Map.empty
          \<and> cm_invar CM 
          \<and> SAT_Basic.models (cm_F CM) 
            = SAT_Basic.models (set (map clause_\<alpha> lst)) 
          \<and> (\<forall>i\<in>cm_ids CM. i<next_id)"
    and Z=litZ and l=lst   
    ])  
  apply (vc_solve)
  apply ((drule (1) lz_string_determ)?; 
      fastforce 
          simp: SAT_Basic.models_def sat_def 
          simp: cm_ids_empty_imp_F_empty itran_invarI)+
  done  
  
definition cm_init_lit 
  :: "var literal \<Rightarrow> clausemap \<Rightarrow> (_,clausemap) enres"
  where "cm_init_lit \<equiv> \<lambda>l (CM,RL). ERETURN (CM,RL(l \<mapsto> {}))"
   
lemma cm_init_lit_correct[THEN ESPEC_trans, refine_vcg]: 
  "\<lbrakk> cm_invar CMRL; cm_ids CMRL = {} \<rbrakk> \<Longrightarrow>
    cm_init_lit l CMRL 
    \<le> ESPEC (\<lambda>_. False) (\<lambda>CMRL'. cm_invar CMRL' \<and> cm_ids CMRL' = {})"  
  unfolding cm_init_lit_def
  apply refine_vcg  
  apply (auto simp: cm_invar_def cm_ids_def ran_def)  
  done  
    
definition "init_rat_counts prf \<equiv> doE {
  (ty,prf) \<leftarrow> parse_type prf;
  CHECK (ty = RAT_COUNTS) (mkp_errprf STR ''Expected RAT counts item'' prf);

  (l,prf) \<leftarrow> parse_prf_literalZ prf;
  (CM,_,prf) \<leftarrow> EWHILET (\<lambda>(CM,l,prf). l\<noteq>None) (\<lambda>(CM,l,prf). doE {
    EASSERT (l\<noteq>None);
    let l = the l;
    (_,prf) \<leftarrow> parse_prf prf;  \<^cancel>\<open> Just ignoring count, silently assuming it to be >0. TODO: Add count-down and stop optimization? \<close>
    
    let l = neg_lit l;
    CM \<leftarrow> cm_init_lit l CM;
    
    (l,prf) \<leftarrow> parse_prf_literalZ prf;
    ERETURN (CM,l,prf)
  }) (cm_empty,l,prf);

  ERETURN (CM,prf)
}"
    
lemma init_rat_counts_correct[THEN ESPEC_trans, refine_vcg]:
  "init_rat_counts prf 
    \<le> ESPEC (\<lambda>_. True) (\<lambda>(CM,prf'). cm_invar CM \<and> cm_ids CM = {} \<and> (prf',prf)\<in>prfWF\<^sup>+)"
  unfolding init_rat_counts_def
  apply (refine_vcg EWHILET_rule[where 
        I="\<lambda>(CM,_,_). cm_invar CM 
                    \<and> cm_ids CM = {}" 
    and R="inv_image (prfWF\<^sup>+) (\<lambda>(_,_,prf). prf)"
      ])
  by (auto dest: rtrancl_inv_image_ssI)
    
  
    
definition "verify_unsat F_begin F_end it prf \<equiv> doE {
  EASSERT (it_invar it);

  (CM,prf) \<leftarrow> init_rat_counts prf;

  CM \<leftarrow> read_cnf_new F_end F_begin CM;

  let s = (CM,Map.empty);

  EWHILEIT 
    (\<lambda>Some (_,it,_) \<Rightarrow> it_invar it | None \<Rightarrow> True) 
    (\<lambda>s. s\<noteq>None) 
    (\<lambda>s. doE {
      EASSERT (s\<noteq>None);
      let (s,it,prf) = the s;
  
      EASSERT (it_invar it); 
  
      check_item s it prf
    }) (Some (s,it,prf));
    
  ERETURN ()
  \<^cancel>\<open>  
  CHECK (is_None s) (mkp_err ''Proof did not contain conflict declaration'')
  \<close>
}"

lemma verify_unsat_correct: 
  "\<lbrakk>seg F_begin lst F_end; it_invar F_end; it_invar it\<rbrakk> \<Longrightarrow> 
    verify_unsat F_begin F_end it prf
    \<le> ESPEC (\<lambda>_. True) (\<lambda>_. F_invar lst \<and> \<not>sat (F_\<alpha> lst))"
  unfolding verify_unsat_def
  apply (refine_vcg 
    EWHILEIT_expinv_rule[where 
          I="\<lambda>
            (None) \<Rightarrow> \<not>sat (F_\<alpha> lst)
          | (Some ((CM,A), it', prf')) \<Rightarrow> it_invar it'
                \<and> cm_invar CM 
                \<and> (sat (F_\<alpha> lst) \<longrightarrow> sat' (cm_F CM) A)"
      and R="inv_image (less_than <*lex*> prfWF\<^sup>+) (\<lambda>None \<Rightarrow> (0::nat,undefined) | Some (_,_,prf) \<Rightarrow> (1,prf))"
      ]
    )
  apply vc_solve
  apply assumption  
  applyS (auto)
  applyS (auto simp: F_\<alpha>_def F_invar_def)
  applyS (clarsimp split: option.splits; auto)
  applyS (auto split!: option.split_asm)
  applyS (auto simp: F_\<alpha>_def F_invar_def)
  applyS (auto split: option.split_asm)
  applyS (auto split: option.split_asm)
  done    
    
    
end \<comment> \<open>proof parser\<close>  

subsection \<open>Refinement --- Backtracking\<close>

type_synonym bt_assignment = "(var \<rightharpoonup> bool) \<times> var set"

definition "backtrack A T \<equiv> A|`(-T)"
lemma backtrack_empty[simp]: "backtrack A {} = A" 
  unfolding backtrack_def by auto

definition "is_backtrack A' T' A \<equiv> T'\<subseteq>dom A' \<and> A = backtrack A' T'"
lemma is_backtrack_empty[simp]: "is_backtrack A {} A" 
  unfolding is_backtrack_def by auto
lemma is_backtrack_not_undec: 
  "\<lbrakk> is_backtrack A' T' A; var_of_lit l\<in>T' \<rbrakk> \<Longrightarrow> sem_lit' l A' \<noteq> None"
  unfolding is_backtrack_def apply (cases l) by auto

lemma is_backtrack_assignI: 
  "\<lbrakk>is_backtrack A' T' A; sem_lit' l A' = None; x = var_of_lit l\<rbrakk> 
  \<Longrightarrow> is_backtrack (assign_lit A' l) (insert x T') A"
  unfolding is_backtrack_def backtrack_def
  apply (cases l; simp; intro conjI)
  by (auto simp: restrict_map_def)


context unsat_input begin

definition "assign_lit_bt \<equiv> \<lambda>A T l. doE {
  EASSERT (sem_lit' l A = None \<and> var_of_lit l \<notin> T);
  ERETURN (assign_lit A l, insert (var_of_lit l) T)
}"

definition "apply_unit_bt i CM A T \<equiv> doE {
  C \<leftarrow> resolve_id CM i;
  l \<leftarrow> check_unit_clause A C;
  assign_lit_bt A T l
}"

definition "apply_units_bt CM A T prf \<equiv> doE {
  (i,prf) \<leftarrow> parse_idZ prf;
  ((A,T),i,prf) \<leftarrow> EWHILET 
    (\<lambda>((A,T),i,prf). i\<noteq>0) 
    (\<lambda>((A,T),i,prf). doE {
      (A,T) \<leftarrow> apply_unit_bt i CM A T;
      (i,prf) \<leftarrow> parse_idZ prf;
      ERETURN ((A,T),i,prf)
    }) ((A,T),i,prf);
  ERETURN ((A,T),prf)
}"

definition "parse_check_blocked_bt A it \<equiv> doE {EASSERT (it_invar it); ESPEC 
  (\<lambda>_. True \<^cancel>\<open>\<lambda>e. parse_clause it = Inl e\<close>) 
  (\<lambda>(C,(A',T'),it'). \<exists>l. 
      lz_string litZ it l it' 
    \<and> it_invar it' 
    \<and> C=clause_\<alpha> l 
    \<and> \<not>is_blocked A C 
    \<and> A' = and_not_C A C 
    \<and> T' = { v. v\<in>var_of_lit`C \<and> A v = None })}"

definition "and_not_C_bt A C \<equiv> doE {
  EASSERT (\<not>is_blocked A C);
  ERETURN (and_not_C A C, { v. v\<in>var_of_lit`C \<and> A v = None })
}"

definition "check_candidates' candidates A prf check \<equiv> doE {
  (cand,prf) \<leftarrow> parse_idZ prf;
  (candidates,A,cand,prf) \<leftarrow> EWHILET
    (\<lambda>(_,_,cand,_). cand\<noteq>0)
    (\<lambda>(candidates,A,cand,prf). doE {
      if cand \<in> candidates then doE {
        let candidates = candidates - {cand};
        (A,prf) \<leftarrow> check cand A prf;
        (cand,prf) \<leftarrow> parse_idZ prf;
        ERETURN (candidates,A,cand,prf)
      } else doE {
        prf \<leftarrow> parse_skip_listZ prf;
        (_,prf) \<leftarrow> parse_prf prf;
        (cand,prf) \<leftarrow> parse_idZ prf;
        ERETURN (candidates,A,cand,prf)
      }
    }) (candidates,A,cand,prf);

  CHECK (candidates = {}) (mkp_errprf STR ''Too few RAT-candidates in proof'' prf);
  ERETURN (A,prf)
}"

lemma check_candidates'_refine_ca[refine]:
  assumes [simplified,simp]: "(candidatesi,candidates)\<in>Id" "(prfi,prf)\<in>Id"
  assumes [refine]: "\<And>candi prfi cand prf A'. 
      \<lbrakk>(candi,cand)\<in>Id; (prfi,prf)\<in>Id; (A',A)\<in>Id\<rbrakk> 
      \<Longrightarrow> check' candi A' prfi 
            \<le>\<Down>\<^sub>E UNIV ({((A,prf),prf) | prf. True }) 
          (check cand prf)"
  shows "check_candidates' candidatesi A prfi check' 
          \<le>\<Down>\<^sub>E UNIV {((A,prf),prf) | prf. True } 
        (check_candidates candidates prf check)"
  unfolding check_candidates'_def check_candidates_def                                     
  apply refine_rcg
  supply RELATESI[where R="{((c,A,prf),(c,prf))| c prf. True}", refine_dref_RELATES]
  supply RELATESI[where R="{((A,prf),prf) | prf. True }", refine_dref_RELATES]
  apply refine_dref_type
  apply (vc_solve simp: RELATES_def)
  done

lemma check_candidates'_refine[refine]:
  assumes [simplified,simp]: 
    "(candidatesi,candidates)\<in>Id" "(prfi,prf)\<in>Id" "(Ai,A)\<in>Id"
  assumes ERID: "Id \<subseteq> ER"  
  assumes [refine]: 
    "\<And>candi prfi cand prf A' A. \<lbrakk>(candi,cand)\<in>Id; (prfi,prf)\<in>Id; (A',A)\<in>Id\<rbrakk> 
      \<Longrightarrow> check' candi A' prfi \<le>\<Down>\<^sub>E ER (Id\<times>\<^sub>rId) (check cand A prf)"
  shows "check_candidates' candidatesi Ai prfi check' 
        \<le>\<Down>\<^sub>E ER (Id\<times>\<^sub>rId) (check_candidates' candidates A prf check)"
  unfolding check_candidates'_def check_candidates_def
  apply refine_rcg
  apply refine_dref_type
  using ERID
  apply (vc_solve solve: asm_rl)
  done



definition check_rup_proof_bt :: "state \<Rightarrow> 'it \<Rightarrow> (nat\<times>'prf) \<Rightarrow> (_, state \<times> 'it \<times> (nat\<times>'prf)) enres" where
  "check_rup_proof_bt \<equiv> \<lambda>(CM,A) it prf. doE {
    (i,prf) \<leftarrow> parse_id prf;
    CHECK (i\<notin>cm_ids CM) (mkp_errNprf STR ''Duplicate ID'' i prf);
    (C,(A,T),it) \<leftarrow> parse_check_blocked_bt A it;
    ((A,T),prf) \<leftarrow> apply_units_bt CM A T prf;
    (confl_id,prf) \<leftarrow> parse_id prf;
    confl \<leftarrow> resolve_id CM confl_id;
    CHECK (is_conflict_clause A confl)
          (mkp_errNprf STR ''Expected conflict clause'' confl_id prf);
    EASSERT (i \<notin> cm_ids CM);
    CM \<leftarrow> add_clause i C CM;
    ERETURN ((CM,backtrack A T),it,prf)
  }"

definition check_rat_proof_bt :: "state \<Rightarrow> 'it \<Rightarrow> (nat \<times> 'prf) \<Rightarrow> (_,state \<times> 'it \<times> (nat \<times> 'prf)) enres" where
  "check_rat_proof_bt \<equiv> \<lambda>(CM,A) it prf. doE {
    (reslit,prf) \<leftarrow> parse_prf_literal prf;

    CHECK (sem_lit' reslit A \<noteq> Some False) 
          (mkp_errprf STR ''Resolution literal is false'' prf);
    (i,prf) \<leftarrow> parse_id prf;
    CHECK (i\<notin>cm_ids CM) (mkp_errNprf STR ''Duplicate ID'' i prf);
    (C,(A,T),it) \<leftarrow> parse_check_blocked_bt A it;
    CHECK (reslit \<in> C) (mkp_errprf STR ''Resolution literal not in clause'' prf);
    ((A,T),prf) \<leftarrow> apply_units_bt CM A T prf;
    candidates \<leftarrow> get_rat_candidates CM A reslit;
    (A,prf) \<leftarrow> check_candidates' candidates A prf (\<lambda>cand_id A prf. doE {
      cand \<leftarrow> resolve_id CM cand_id;

      (A,T2) \<leftarrow> and_not_C_bt A (cand-{neg_lit reslit});
      ((A,T2),prf) \<leftarrow> apply_units_bt CM A T2 prf;
      (confl_id,prf) \<leftarrow> parse_id prf;
      confl \<leftarrow> resolve_id CM confl_id;
      CHECK (is_conflict_clause A confl) 
            (mkp_errprf STR ''Expected conflict clause'' prf);
      ERETURN (backtrack A T2,prf)
    });

    EASSERT (i \<notin> cm_ids CM);
    CM \<leftarrow> add_clause i C CM;
    ERETURN ((CM,backtrack A T),it,prf)
  }"

definition "bt_assign_rel A 
  \<equiv> { ((A',T),A') | A' T. T \<subseteq> dom A' \<and> A = A'|`(-T) }"
definition "bt_need_bt_rel A\<^sub>0 
  \<equiv> br (\<lambda>_. A\<^sub>0) (\<lambda>(A',T'). T'\<subseteq>dom A' \<and> backtrack A' T' = A\<^sub>0)"
  
\<^cancel>\<open>definition "bt_anccb_rel A\<^sub>0 \<equiv> 
    ({(False,False)} \<times>\<^sub>r Id \<times>\<^sub>r bt_assign_rel A\<^sub>0 \<times>\<^sub>r Id) 
  \<union> ({(True,True)} \<times>\<^sub>r UNIV \<times>\<^sub>r bt_need_bt_rel A\<^sub>0 \<times>\<^sub>r UNIV)"
\<close>

lemma bt_rel_simps:
  "((Ai,T),A)\<in>bt_assign_rel A\<^sub>0 \<Longrightarrow> Ai=A \<and> backtrack A T = A\<^sub>0 \<and> T\<subseteq>dom A"
  "((Ai,T),A)\<in>bt_need_bt_rel A\<^sub>0 \<Longrightarrow> A=A\<^sub>0 \<and> backtrack Ai T = A\<^sub>0 \<and> T\<subseteq>dom Ai"
  unfolding bt_assign_rel_def bt_need_bt_rel_def 
  by (auto simp: backtrack_def in_br_conv)

lemma bt_in_bta_rel: "T \<subseteq> dom A \<Longrightarrow> ((A,T),A)\<in>bt_assign_rel (backtrack A T)"
  by (auto simp: bt_assign_rel_def backtrack_def)


lemma and_not_C_bt_refine[refine]: "\<lbrakk> \<not>is_blocked A C; (Ai,A)\<in>Id; (Ci,C)\<in>Id \<rbrakk> 
  \<Longrightarrow> and_not_C_bt Ai Ci \<le>\<Down>\<^sub>E UNIV (bt_assign_rel A) (ERETURN (and_not_C A C))"
  apply (auto 
      simp: pw_ele_iff refine_pw_simps
      simp: and_not_C_bt_def and_not_C_def bt_assign_rel_def restrict_map_def 
      split!: if_splits intro!: ext)
  apply force
  apply force
  apply (metis var_of_lit.elims)
  apply force
  apply force
  apply (force simp: is_blocked_alt sem_clause'_true_conv)
  apply (force simp: is_blocked_alt sem_clause'_true_conv)
  done  

lemma parse_check_blocked_bt_refine[refine]: "\<lbrakk> (Ai,A)\<in>Id; (iti,it)\<in>Id \<rbrakk> 
  \<Longrightarrow> parse_check_blocked_bt Ai iti 
    \<le> \<Down>\<^sub>E UNIV (Id \<times>\<^sub>r bt_assign_rel A \<times>\<^sub>r Id) (parse_check_blocked A it)"
  unfolding parse_check_blocked_bt_def parse_check_blocked_def
  apply clarsimp
  apply (refine_rcg)  
  apply (clarsimp simp: econc_fun_ESPEC; rule ESPEC_rule)
  apply (clarsimp simp: bt_assign_rel_def; safe; simp?)  

  subgoal for _ _ lit
    by (cases "lit"; auto simp: and_not_C_def; force)

  subgoal
    apply (
      clarsimp 
        simp: and_not_C_def restrict_map_def is_blocked_def 
        intro!: ext; 
      safe)
    apply (force|force simp: sem_clause'_true_conv)+
    done
  subgoal by auto    
  done    
  
lemma assign_lit_bt_refine[refine]: 
  "\<lbrakk> sem_lit' l A = None; ((Ai,Ti),A)\<in>bt_assign_rel A\<^sub>0; (li,l)\<in>Id \<rbrakk> 
  \<Longrightarrow> assign_lit_bt Ai Ti li 
      \<le>\<Down>\<^sub>E UNIV (bt_assign_rel A\<^sub>0) (ERETURN (assign_lit A l))"
  unfolding assign_lit_bt_def assign_lit_def bt_assign_rel_def
  apply refine_vcg
  applyS simp
  subgoal by (cases l) auto
  subgoal by (cases l; auto simp: restrict_map_def intro!: ext)
  done
  
lemma apply_unit_bt_refine[refine]: 
  "\<lbrakk> (ii,i)\<in>Id; (CMi,CM)\<in>Id; ((Ai,Ti),A)\<in>bt_assign_rel A\<^sub>0 \<rbrakk> 
  \<Longrightarrow> apply_unit_bt ii CMi Ai Ti 
      \<le>\<Down>\<^sub>E UNIV (bt_assign_rel A\<^sub>0) (apply_unit i CM A)"
  unfolding apply_unit_bt_def apply_unit_def
  apply refine_rcg
  apply refine_dref_type
  apply (vc_solve dest!: bt_rel_simps) 
  done

lemma apply_units_bt_refine[refine]: 
  "\<lbrakk> (CMi,CM)\<in>Id; ((Ai,Ti),A)\<in>bt_assign_rel A\<^sub>0; (iti,it)\<in>Id \<rbrakk> 
  \<Longrightarrow> apply_units_bt CMi Ai Ti iti 
      \<le>\<Down>\<^sub>E UNIV (bt_assign_rel A\<^sub>0 \<times>\<^sub>r Id) (apply_units CM A it)"
  unfolding apply_units_bt_def apply_units_def
  supply RELATESI[of "bt_assign_rel A" for A, refine_dref_RELATES]
  apply refine_rcg
  apply refine_dref_type
  apply auto
  done

term check_rup_proof
lemma check_rup_proof_bt_refine[refine]:
  "\<lbrakk> (si,s)\<in>Id; (iti,it)\<in>Id; (prfi,prf)\<in>Id \<rbrakk> 
  \<Longrightarrow> check_rup_proof_bt si iti prfi \<le>\<Down>\<^sub>E UNIV Id (check_rup_proof s it prf)"
  unfolding check_rup_proof_bt_def check_rup_proof_def
  apply refine_rcg
  apply refine_dref_type
  apply (auto simp: bt_in_bta_rel dest!: bt_rel_simps)
  done
  
lemma check_rat_proof_bt_refine[refine]:
  "\<lbrakk> (si,s)\<in>Id; (iti,it)\<in>Id; (prfi,prf)\<in>Id \<rbrakk> 
  \<Longrightarrow> check_rat_proof_bt si iti prfi \<le>\<Down>\<^sub>E UNIV Id (check_rat_proof s it prf)"
  unfolding check_rat_proof_bt_def check_rat_proof_def
  apply refine_rcg
  apply refine_dref_type
  apply (auto simp: bt_in_bta_rel dest!: bt_rel_simps) \<^cancel>\<open> Takes long \<close>
  done
  

definition check_item_bt :: "state \<Rightarrow> 'it \<Rightarrow> (nat \<times> 'prf) \<Rightarrow> (_, (state \<times> 'it \<times> (nat \<times> 'prf)) option) enres"
  where "check_item_bt \<equiv> \<lambda>(CM,A) it prf. doE {
    (ty,prf) \<leftarrow> parse_type prf;
    case ty of
      INVALID \<Rightarrow> THROW (mkp_err STR ''Invalid item'')
    | UNIT_PROP \<Rightarrow> doE {
        (A,prf) \<leftarrow> apply_units CM A prf;
        ERETURN (Some ((CM,A),it,prf))
      }
    | DELETION \<Rightarrow> doE {
        (CM,prf) \<leftarrow> remove_ids CM prf;
        ERETURN (Some ((CM,A),it,prf))
      }
    | RUP_LEMMA \<Rightarrow> doE {
        s \<leftarrow> check_rup_proof_bt (CM,A) it prf;
        ERETURN (Some s)
      }
    | RAT_LEMMA \<Rightarrow> doE {
        s \<leftarrow> check_rat_proof_bt (CM,A) it prf;
        ERETURN (Some s)
      }
    | CONFLICT \<Rightarrow> doE {
        (i,prf) \<leftarrow> parse_id prf;
        C \<leftarrow> resolve_id CM i;
        CHECK (is_conflict_clause A C) 
              (mkp_errNprf STR ''Conflict clause has no conflict'' i prf);
        ERETURN None
      }
    | RAT_COUNTS \<Rightarrow> 
        THROW (mkp_errprf STR ''Not expecting rat-counts in the middle of proof'' prf)
  }"

lemma check_item_bt_refine[refine]: "\<lbrakk>(si,s)\<in>Id; (iti,it)\<in>Id; (prfi,prf)\<in>Id\<rbrakk> 
  \<Longrightarrow> check_item_bt si iti prfi \<le>\<Down>\<^sub>E UNIV Id (check_item s it prf)"
  unfolding check_item_bt_def check_item_def
  apply refine_rcg
  apply refine_dref_type
  applyS simp
  
  subgoal
    apply (split item_type.split; intro impI conjI; simp)
    apply (refine_rcg; auto)
    apply (refine_rcg; auto)
    done
  done

definition "verify_unsat_bt F_begin F_end it prf \<equiv> doE {
  EASSERT (it_invar it);

  (CM,prf) \<leftarrow> init_rat_counts prf;

  CM \<leftarrow> read_cnf_new F_end F_begin CM;

  let s = (CM,Map.empty);

  EWHILEIT 
    (\<lambda>Some (_,it,_) \<Rightarrow> it_invar it | None \<Rightarrow> True) 
    (\<lambda>s. s\<noteq>None) 
    (\<lambda>s. 
  doE {
    EASSERT (s\<noteq>None);
    let (s,it,prf) = the s;

    EASSERT (it_invar it); 

    check_item_bt s it prf
  }) (Some (s,it,prf));
  ERETURN ()
  \<^cancel>\<open>CHECK (is_None s) (mkp_err ''Proof did not contain conflict declaration'')\<close>
}"

lemma verify_unsat_bt_refine[refine]: 
  "\<lbrakk> (F_begini,F_begin)\<in>Id; (F_endi,F_end)\<in>Id; (iti,it)\<in>Id; (prfi,prf)\<in>Id \<rbrakk> 
  \<Longrightarrow> verify_unsat_bt F_begini F_endi iti prfi
      \<le>\<Down>\<^sub>E UNIV Id (verify_unsat F_begin F_end it prf)"
  unfolding verify_unsat_bt_def verify_unsat_def
  apply refine_rcg
  apply refine_dref_type
  apply vc_solve
  done

end \<comment> \<open>proof parser\<close>

subsection \<open>Refinement 1\<close>
text \<open>Model clauses by iterators to their starting position\<close>

type_synonym ('it) clausemap1 = "(id \<rightharpoonup> 'it) \<times> (var literal \<rightharpoonup> id list)"
type_synonym ('it) state1 = "('it) clausemap1 \<times> (var \<rightharpoonup> bool)"

context unsat_input begin

  definition "cref_rel 
    \<equiv> { (cref,C). \<exists>l it'. lz_string litZ cref l it' 
                        \<and> it_invar it' 
                        \<and> C = clause_\<alpha> l}"
  definition "next_it_rel 
    \<equiv> { (cref,it'). \<exists>l. lz_string litZ cref l it' \<and> it_invar it'}"

  definition "clausemap1_rel 
    \<equiv> (Id \<rightarrow> \<langle>cref_rel\<rangle>option_rel) \<times>\<^sub>r (Id \<rightarrow> \<langle>br set (\<lambda>_. True)\<rangle>option_rel)"
  abbreviation "state1_rel \<equiv> clausemap1_rel \<times>\<^sub>r Id"
  
  definition "parse_check_clause cref c f s \<equiv> doE { 
    (it,s) \<leftarrow> parse_lz (mkp_err STR ''Parsed beyond end'') litZ it_end cref c (\<lambda>x s. doE {
      EASSERT (x \<noteq> litZ);
      let l = lit_\<alpha> x;
      f l s
    }) s; 
    ERETURN (s,it)
  }"
    
  lemma parse_check_clause_rule_aux:
    assumes I[simp]: "I {} s"
    assumes F_RL: 
      "\<And>C l s. \<lbrakk>I C s; c s\<rbrakk> \<Longrightarrow> f l s \<le> ESPEC (\<lambda>_. True) (I (insert l C))"
    assumes [simp]: "it_invar cref"
    shows "parse_check_clause cref c f s \<le> ESPEC 
      (\<^cancel>\<open> TODO: Spec that parsing failed \<close> \<lambda>_. True) 
      (\<lambda>(s,it'). \<exists>C. 
          I C s
        \<and> (c s \<longrightarrow> it_invar it' 
                 \<and> (cref,C) \<in> cref_rel 
                 \<and> (cref,it') \<in> next_it_rel)
      )"
    unfolding parse_check_clause_def  
    apply (refine_vcg parse_lz_rule[where \<Phi>="\<lambda>l s. I (clause_\<alpha> l) s"])  
    apply (vc_solve simp: F_RL)
    apply (auto simp: cref_rel_def next_it_rel_def dest!: itran_invarD)  
    done  
  
  lemma parse_check_clause_rule:
    assumes I0: "I {} s"
    assumes [simp]: "it_invar cref"
    assumes F_RL: 
      "\<And>C l s. \<lbrakk>I C s; c s\<rbrakk> \<Longrightarrow> f l s \<le> ESPEC (\<lambda>_. True) (I (insert l C))"
    assumes "\<And>C s it'. \<lbrakk>I C s; \<not>c s \<rbrakk> \<Longrightarrow> Q (s,it')"  
    assumes "\<And>C s it'. 
      \<lbrakk> I C s; c s; (cref,it')\<in>next_it_rel; (cref,C)\<in>cref_rel \<rbrakk> \<Longrightarrow> Q (s,it')"  
    shows "parse_check_clause cref c f s \<le> ESPEC (\<lambda>_. True) Q"
    apply (rule order_trans)  
    apply (rule parse_check_clause_rule_aux[of I, OF I0])
    apply (erule (1) F_RL)
    apply fact
    using assms(4,5) 
    by (fastforce simp: ESPEC_rule_iff next_it_rel_def cref_rel_def)
  

  \<^cancel>\<open> Iterate over already parsed clause \<close>
  definition "iterate_clause cref c f s \<equiv> 
    iterate_lz litZ it_end cref c (\<lambda>x s. f (lit_\<alpha> x) s) s"
  
  lemma iterate_clause_rule:
    assumes CR: "(cref,C)\<in>cref_rel"
    assumes I0: "I {} s"
    assumes F_RL: "\<And>C1 l s. 
      \<lbrakk> I C1 s; C1\<subseteq>C; l\<in>C; c s \<rbrakk> \<Longrightarrow> f l s \<le> ESPEC E (I (insert l C1))"
    assumes T_IMP: "\<And>s. \<lbrakk> c s; I C s \<rbrakk> \<Longrightarrow> P s"  
    assumes C_IMP: "\<And>s C1. \<lbrakk> \<not>c s; C1\<subseteq>C; I C1 s \<rbrakk> \<Longrightarrow> P s"  
    shows "iterate_clause cref c f s \<le> ESPEC E P"
  proof -
    from CR obtain l it' where 
            ISLZ: "lz_string litZ cref l it'" 
      and INV: "it_invar it'"      
      and [simp]: "C = clause_\<alpha> l" 
      by (auto simp: cref_rel_def)
    
    show ?thesis
      unfolding iterate_clause_def
      apply (refine_vcg 
          iterate_lz_rule[OF ISLZ, where \<Phi>="\<lambda>l1 l2 s. I (clause_\<alpha> l1) s"])  
      apply vc_solve  
      applyS (simp add: INV itran_ord)
      applyS (simp add: I0)  
      applyS (rule F_RL; auto)  
      applyS (erule C_IMP; assumption?; auto)  
      applyS (auto intro: T_IMP)  
      done  
  qed      
  
  definition "check_unit_clause1 A cref \<equiv> doE {
    ul \<leftarrow> iterate_clause cref (\<lambda>ul. True) (\<lambda>l ul. doE {
      CHECK (sem_lit' l A \<noteq> Some True) 
            (mkp_err STR ''True literal in clause assumed to be unit'');
      if (sem_lit' l A = Some False) then ERETURN ul
      else doE {
        CHECK (ul = None \<or> ul = Some l) 
              (mkp_err STR ''2-undec in clause assumed to be unit'');
        ERETURN (Some l)
      }
    }) None;
    CHECK (ul \<noteq> None) (mkp_err STR ''Conflict in clause assumed to be unit'');
    EASSERT (ul \<noteq> None);
    ERETURN (the ul)
  }"

  lemma check_unit_clause1_refine[refine]:
    assumes [simplified, simp]: "(Ai,A)\<in>Id"
    assumes CR: "(cref,C)\<in>cref_rel"
    shows "check_unit_clause1 Ai cref \<le>\<Down>\<^sub>EUNIV Id (check_unit_clause A C)"
    unfolding check_unit_clause1_def check_unit_clause_def econc_fun_univ_id
    apply refine_vcg
    apply (refine_vcg iterate_clause_rule[OF CR, where 
          I="\<lambda>C' ul. case ul of 
                None \<Rightarrow> sem_clause' C' A = Some False 
              | Some l \<Rightarrow> is_unit_lit A C' l"]
        )
    apply (auto split: option.splits simp: is_unit_clause_def)
    subgoal by (smt Diff_iff insert_iff is_unit_lit_def sem_clause'_false_conv)
    subgoal by (smt Diff_empty Diff_insert0 boolopt_cases_aux.cases 
                    insertI1 insert_Diff1 is_unit_lit_def 
                    sem_clause'_false_conv)
    subgoal by (simp add: is_unit_lit_def)
    subgoal apply (drule (2) is_unit_lit_unique_ss) 
      using sem_not_false_the_unit_lit by blast 
    subgoal using is_unit_clauseI unit_contains_no_true by blast    
    subgoal using is_unit_clauseI unit_contains_no_true by blast    
    subgoal by (simp add: unit_clause_sem')
    done

  
  definition "resolve_id1 \<equiv> \<lambda>(CM,_) i. doE {
    CHECK (i\<in>dom CM) (mkp_errN STR ''Invalid clause id'' i);
    ERETURN (the (CM i))
  }"
    
  lemma resolve_id1_refine[refine]:
    "\<lbrakk> (CMi,CM)\<in>clausemap1_rel; (ii,i)\<in>Id \<rbrakk> 
    \<Longrightarrow> resolve_id1 CMi ii \<le>\<Down>\<^sub>EUNIV cref_rel (resolve_id CM i)"
    unfolding resolve_id1_def resolve_id_def clausemap1_rel_def
    apply (cases CM; cases CMi)
    apply (clarsimp simp: pw_ele_iff refine_pw_simps)
    apply (auto dest!: fun_relD[where x=i and x'=i]  elim: option_relE)
    done
  
  definition "apply_unit1_bt i CM A T \<equiv> doE {
    C \<leftarrow> resolve_id1 CM i;
    l \<leftarrow> check_unit_clause1 A C;
    assign_lit_bt A T l
  }"
  
  lemma apply_unit1_bt_refine[refine]: 
    "\<lbrakk> (ii,i)\<in>Id; (CMi,CM)\<in>clausemap1_rel; (Ai,A)\<in>Id; (Ti,T)\<in>Id \<rbrakk> 
    \<Longrightarrow> apply_unit1_bt ii CMi Ai Ti \<le> \<Down>\<^sub>EUNIV Id (apply_unit_bt i CM A T)"
    unfolding apply_unit_bt_def apply_unit1_bt_def
    apply refine_rcg
    apply (vc_solve)
    done

  definition "apply_units1_bt CM A T prf \<equiv> doE {
    (i,prf) \<leftarrow> parse_idZ prf;
    ((A,T),i,prf) \<leftarrow> EWHILET 
      (\<lambda>((A,T),i,prf). i\<noteq>0) 
      (\<lambda>((A,T),i,prf). doE {
        (A,T) \<leftarrow> apply_unit1_bt i CM A T;
        (i,prf) \<leftarrow> parse_idZ prf;
        ERETURN ((A,T),i,prf)
      }) ((A,T),i,prf);
    ERETURN ((A,T),prf)
  }"
  
  lemma apply_units1_bt_refine[refine]: 
    "\<lbrakk> (CMi,CM)\<in>clausemap1_rel; (Ai,A)\<in>Id; (Ti,T)\<in>Id; (iti,it)\<in>Id \<rbrakk> 
    \<Longrightarrow> apply_units1_bt CMi Ai Ti iti \<le> \<Down>\<^sub>E UNIV Id (apply_units_bt CM A T it)"
    unfolding apply_units1_bt_def apply_units_bt_def
    apply refine_rcg
    apply refine_dref_type
    apply vc_solve
    done  
  
  definition "apply_unit1 i CM A \<equiv> doE {
    C \<leftarrow> resolve_id1 CM i;
    l \<leftarrow> check_unit_clause1 A C;
    ERETURN (assign_lit A l)
  }"
  
  lemma apply_unit1_refine[refine]: 
    "\<lbrakk> (ii,i)\<in>Id; (CMi,CM)\<in>clausemap1_rel; (Ai,A)\<in>Id \<rbrakk> 
    \<Longrightarrow> apply_unit1 ii CMi Ai \<le> \<Down>\<^sub>EUNIV Id (apply_unit i CM A)"
    unfolding apply_unit_def apply_unit1_def
    apply refine_rcg
    apply (vc_solve)
    done
  
  definition "apply_units1 CM A prf \<equiv> doE {
    (i,prf) \<leftarrow> parse_idZ prf;
    (A,i,prf) \<leftarrow> EWHILET 
      (\<lambda>(A,i,prf). i\<noteq>0) 
      (\<lambda>(A,i,prf). doE {
        A \<leftarrow> apply_unit1 i CM A;
        (i,prf) \<leftarrow> parse_idZ prf;
        ERETURN (A,i,prf)
      }) (A,i,prf);
    ERETURN (A,prf)
  }"
  
  lemma apply_units1_refine[refine]: 
    "\<lbrakk> (CMi,CM)\<in>clausemap1_rel; (Ai,A)\<in>Id; (iti,it)\<in>Id \<rbrakk> 
    \<Longrightarrow> apply_units1 CMi Ai iti \<le> \<Down>\<^sub>E UNIV Id (apply_units CM A it)"
    unfolding apply_units1_def apply_units_def
    apply refine_rcg
    apply refine_dref_type
    apply vc_solve
    done  


  lemma dom_and_not_C_diff_aux: "\<lbrakk>\<not>is_blocked A C\<rbrakk> 
    \<Longrightarrow> dom (and_not_C A C) - dom A = {v \<in> var_of_lit ` C. A v = None}"
    apply (auto simp: is_blocked_def sem_clause'_true_conv)
    apply (auto simp: dom_def and_not_C_def split: if_split_asm)
    apply force
    apply force
    subgoal for l by (cases l) auto
    done
    
  lemma dom_and_not_C_eq: "dom (and_not_C A C) = dom A \<union> var_of_lit`C"
    apply (safe; clarsimp?)
    apply (force simp: and_not_C_def dom_def split: if_split_asm) []
    apply (force simp: and_not_C_def) []
    subgoal for l by (cases l) (auto simp: and_not_C_def)
    done
    
  lemma backtrack_and_not_C_trail_eq: "\<lbrakk> is_backtrack (and_not_C A C) T A\<rbrakk>
         \<Longrightarrow> T = {v \<in> var_of_lit ` C. A v = None}"  
    apply (safe; clarsimp?)
    subgoal
      apply (clarsimp 
              simp: is_backtrack_def backtrack_def 
              simp: dom_and_not_C_eq restrict_map_def)
      apply (frule (1) set_rev_mp; clarsimp) 
      apply (metis option.distinct(1))
      done
    subgoal
      apply (clarsimp simp: is_backtrack_def backtrack_def restrict_map_def)
      by meson
    subgoal
      apply (clarsimp simp: is_backtrack_def backtrack_def restrict_map_def)
      by (metis sem_lit'_none_conv sem_lit_and_not_C_None_conv)
    done  

  definition "parse_check_blocked1 A\<^sub>0 cref \<equiv> doE {
    ((A,T),it') \<leftarrow> parse_check_clause cref (\<lambda>_. True) (\<lambda>l (A,T). doE {
      CHECK (sem_lit' l A \<noteq> Some True) (mkp_err STR ''Blocked lemma clause'');
      if (sem_lit' l A = Some False) then ERETURN (A,T)
      else doE {
        EASSERT (sem_lit' l A = None);
        EASSERT (var_of_lit l \<notin> T);
        ERETURN (assign_lit A (neg_lit l),insert (var_of_lit l) T)
      }
    }) (A\<^sub>0,{});
    ERETURN (cref,(A,T),it')
  }"
    
  lemma parse_check_blocked1_refine[refine]:
    assumes [simplified, simp]: "(Ai,A)\<in>Id" "(iti,it)\<in>Id"
    shows "parse_check_blocked1 Ai iti 
      \<le> \<Down>\<^sub>E UNIV (cref_rel \<times>\<^sub>r Id \<times>\<^sub>r Id) (parse_check_blocked_bt A it)"
    unfolding parse_check_blocked_bt_def      
    apply refine_rcg  
    unfolding econc_fun_ESPEC
    apply simp
    unfolding parse_check_blocked1_def
    apply (refine_vcg
        parse_check_clause_rule[where I="\<lambda>C (A',T'). 
          is_backtrack A' T' A 
        \<and> \<not>is_blocked A C 
        \<and> A' = and_not_C A C
      "]
    )
    apply (vc_solve 
             simp: and_not_insert_False 
             simp: is_backtrack_assignI is_backtrack_not_undec)
      
    subgoal by (auto 
      simp: is_blocked_insert_iff sem_lit_and_not_C_conv 
      intro: is_blockedI1 is_blockedI2) []
    subgoal by (auto simp: not_Some_bool_if) []
    subgoal by (auto simp: is_blocked_insert_iff sem_lit_and_not_C_None_conv) []
    subgoal by (auto simp: simp: and_not_insert_None) []
    subgoal 
      apply (clarsimp simp: next_it_rel_def cref_rel_def)
      apply (drule (1) lz_string_determ)  
      apply (intro exI conjI; 
              assumption?; 
              auto simp: backtrack_and_not_C_trail_eq; fail)
      done  
    done
    
  definition "check_conflict_clause1 prf\<^sub>0 A cref 
    \<equiv> iterate_clause cref (\<lambda>_. True) (\<lambda>l _. doE {
        CHECK (sem_lit' l A = Some False) 
              (mkp_errprf STR ''Expected conflict clause'' prf\<^sub>0) 
      }) ()"
  
  lemma check_conflict_clause1_refine[refine]:
    assumes [simplified,simp]: "(Ai,A)\<in>Id"
    assumes CR: "(cref,C)\<in>cref_rel"
    shows "check_conflict_clause1 it\<^sub>0 Ai cref 
          \<le>\<Down>\<^sub>E UNIV Id (CHECK (is_conflict_clause A C) msg)"
  proof -    
    have ES_REW: "\<Down>\<^sub>E UNIV Id (CHECK (is_conflict_clause A C) msg) 
      = ESPEC (\<lambda>_. \<not>is_conflict_clause A C) (\<lambda>_. is_conflict_clause A C)"
      by (auto simp: pw_eeq_iff refine_pw_simps) 

    show ?thesis
      unfolding check_conflict_clause1_def ES_REW
      apply (refine_vcg 
          iterate_clause_rule[OF CR, where I="\<lambda>C _. is_conflict_clause A C"])
      by (auto simp: sem_clause'_false_conv)
  qed
  
  definition "lit_in_clause1 cref l \<equiv> doE {
    iterate_clause cref (\<lambda>f. \<not>f) (\<lambda>lx _. doE {
      ERETURN (l=lx) 
    }) False
  }"
  
  lemma lit_in_clause1_correct[THEN ESPEC_trans, refine_vcg]:
    assumes CR: "(cref,C) \<in> cref_rel"
    shows "lit_in_clause1 cref lc \<le> ESPEC (\<lambda>_. False) (\<lambda>r. r \<longleftrightarrow> lc\<in>C)"  
    unfolding lit_in_clause1_def
    apply (refine_vcg iterate_clause_rule[OF CR, where I="\<lambda>C r. r \<longleftrightarrow> lc\<in>C"])
    by auto  
  
  definition "lit_in_clause_and_not_true A cref lc \<equiv> doE {
    f \<leftarrow> iterate_clause cref (\<lambda>f. f\<noteq>2) (\<lambda>l f. doE {
      if (l=lc) then ERETURN 1
      else if (sem_lit' l A = Some True) then ERETURN 2
      else ERETURN f
    }) (0::nat);
    ERETURN (f=1)
  }"
  

  lemma lit_in_clause_and_not_true_correct[THEN ESPEC_trans, refine_vcg]:
    assumes CR: "(cref,C) \<in> cref_rel"
    shows "lit_in_clause_and_not_true A cref lc 
            \<le> ESPEC (\<lambda>_. False) 
                (\<lambda>r. r \<longleftrightarrow> lc\<in>C \<and> sem_clause' (C-{lc}) A \<noteq> Some True)"
    unfolding lit_in_clause_and_not_true_def
    apply (refine_vcg iterate_clause_rule[OF CR, where I="\<lambda>C f. f\<in>{0,1,2} 
              \<and> (f=2 \<longleftrightarrow> sem_clause' (C-{lc}) A = Some True)
              \<and> (f=1 \<longrightarrow> lc\<in>C)
              \<and> (f=0 \<longrightarrow> lc\<notin>C)"])
    by (vc_solve simp: insert_minus_eq sem_clause'_true_conv solve: asm_rl)


  definition "and_not_C_excl A cref exl \<equiv> doE {
    iterate_clause cref (\<lambda>_. True) (\<lambda>l (A,T). doE {
      if (l \<noteq> exl) then doE {
        EASSERT (sem_lit' l A \<noteq> Some True);
        if (sem_lit' l A \<noteq> Some False) then doE {
          EASSERT (var_of_lit l \<notin> T);
          ERETURN (assign_lit A (neg_lit l), insert (var_of_lit l) T)
        } else
          ERETURN (A,T)
      } else 
        ERETURN (A,T)
    }) (A,{})
  }"

  lemma and_not_C_excl_refine[refine]:
    assumes [simplified,simp]: "(Ai,A)\<in>Id"
    assumes CR: "(cref,C) \<in> cref_rel"
    assumes [simplified,simp]: "(exli,exl)\<in>Id"
    \<^cancel>\<open>assumes NBLK: "\<not>is_blocked A (C-{exl})"\<close>
    shows "and_not_C_excl Ai cref exli 
            \<le>\<Down>\<^sub>E UNIV (Id\<times>\<^sub>rId) (and_not_C_bt A (C-{exl}))"
    unfolding and_not_C_bt_def
    apply (rule EASSERT_bind_refine_right)
    apply (simp add: econc_fun_ERETURN)
    unfolding and_not_C_excl_def 
    apply (refine_vcg iterate_clause_rule[OF CR, 
      where I="\<lambda>C' (A',T'). A' = and_not_C A (C' - {exl}) 
                          \<and> is_backtrack A' T' A"])
    apply (vc_solve simp: insert_minus_eq)
    subgoal
      by (auto 
            simp: sem_lit_and_not_C_conv sem_clause'_true_conv is_blocked_alt)
    subgoal 
      by (meson boolopt_cases_aux.cases is_backtrack_not_undec)
    subgoal
      by (metis (full_types) and_not_insert_None boolopt_cases_aux.cases 
                insert_minus_eq)
    subgoal
      by (metis (full_types) boolopt_cases_aux.cases is_backtrack_assignI 
                sem_lit'_none_conv var_of_lit_neg_eq)
    subgoal by (simp add: and_not_insert_False)
    subgoal using backtrack_and_not_C_trail_eq by blast
    done
  
  
  definition get_rat_candidates1 
    :: "('it) clausemap1 \<Rightarrow> (var \<rightharpoonup> bool) \<Rightarrow> var literal \<Rightarrow> (_,id set) enres"
    where
    "get_rat_candidates1 \<equiv> \<lambda>(CM,RL) A l. doE {
      let l = neg_lit l;
      let cands_raw = RL l;
      CHECK (\<not>is_None cands_raw) (mkp_err STR ''Resolution literal not declared'');
      \<^cancel>\<open> Get collected candidates \<close>
      let cands_raw = the cands_raw; 
      \<^cancel>\<open>EASSERT (distinct cands_raw);\<close>
      \<^cancel>\<open> Filter deleted, blocked, and those not containing resolution literal \<close>
      cands \<leftarrow> enfoldli cands_raw (\<lambda>_. True) (\<lambda>i s. doE {
        let cref = CM i;
        if \<not>is_None cref then doE {
          let cref = the cref;
          lant \<leftarrow> lit_in_clause_and_not_true A cref l;
          if lant then doE {
            \<^cancel>\<open>EASSERT (i \<notin> s);\<close>
            ERETURN (insert i s)
          } else ERETURN s
        } else ERETURN s
      }) {};
      ERETURN cands
    }"

\<^cancel>\<open>    
  xxx: Choice: We could 1) either remove duplicates after 
    all candidates have been gathered, or 2) from RL-list before 
    deleted|blocked|contained check  
    
    1) In case of massive duplicates, checks will be repeated.
        However, typically, only a few RAT candidates remain, such that
        simple O(n\<^sup>2) remdup impl can be used.
        Moreover, we do not expect massive duplicates.
    2) In case of long candidate lists, remdups may be expensive 
      or requires efficient DS.
\<close>    
    
  lemma get_rat_candidates1_refine[refine]:
    assumes CMR: "(CMi,CM)\<in>clausemap1_rel"
    assumes [simplified, simp]: "(Ai,A)\<in>Id" "(resliti,reslit)\<in>Id"
    shows "get_rat_candidates1 CMi Ai resliti 
            \<le>\<Down>\<^sub>E UNIV (Id) (get_rat_candidates CM A reslit)"
    unfolding get_rat_candidates1_def get_rat_candidates_def
    apply (rewrite at "Let (RL _) _" in "case CMi of (CM,RL) \<Rightarrow> \<hole>" Let_def)
    apply refine_rcg
    apply refine_dref_type
    apply vc_solve
    subgoal 
      using CMR 
      by (auto 
          simp: clausemap1_rel_def cref_rel_def 
          dest!: fun_relD[where x="neg_lit reslit" and x'="neg_lit reslit"]
          elim: option_relE
          )
    \<^cancel>\<open>subgoal for _ RL _ RLi
      using CMR
      apply (clarsimp simp: clausemap1_rel_def in_br_conv)
      apply (drule fun_relD[where x="neg_lit reslit" and x'="neg_lit reslit"]; 
             simp)
      apply (auto simp: in_br_conv elim: option_relE)
      done\<close>
    subgoal premises prems for CM RL CMi RLi cands_raw 
    proof -
      from CMR prems have
        CM_ref: "(CMi, CM) \<in> Id \<rightarrow> \<langle>cref_rel\<rangle>option_rel" and
        RL_ref: "(RLi, RL) \<in> Id \<rightarrow> \<langle>br set (\<lambda>_. True)\<rangle>option_rel"
        by (auto simp: clausemap1_rel_def in_br_conv)
      
      define cands_rawi where "cands_rawi = the (RLi (neg_lit reslit))"
      from prems fun_relD[OF RL_ref IdI[of "neg_lit reslit"]] 
      have [simp]: "cands_raw = set cands_rawi" \<^cancel>\<open>"distinct cands_rawi"\<close>
        unfolding cands_rawi_def by (auto simp: in_br_conv elim: option_relE)
      note cands_rawi_def[symmetric,simp]
      
      show ?thesis
        apply (refine_vcg enfoldli_rule[where I="\<lambda>l1 l2 s. 
              \<^cancel>\<open>distinct (l1@l2) 
            \<and>\<close> s = { i\<in>set l1. \<exists>C. 
                      CM i = Some C 
                    \<and> neg_lit reslit\<in>C 
                    \<and> sem_clause' (C - {neg_lit reslit}) A \<noteq> Some True }"])
        apply vc_solve
        
        subgoal for i l1 l2 
          using fun_relD[OF CM_ref IdI[of i]]
          by (auto elim: option_relE simp: cref_rel_def in_br_conv)
        focus apply (rename_tac i l1 l2)
          apply (subgoal_tac "(the (CMi i), the (CM i)) \<in> cref_rel", assumption)
          subgoal for i l1 l2 
            using fun_relD[OF CM_ref IdI[of i]]
            by (force elim!: option_relE simp: cref_rel_def in_br_conv) \<^cancel>\<open> Takes some time \<close>
        solved
        subgoal for i l1 l2 
          using fun_relD[OF CM_ref IdI[of i]]
          by (auto elim!: option_relE simp: cref_rel_def in_br_conv)
        subgoal for i l1 l2 
          using fun_relD[OF CM_ref IdI[of i]]
          by (auto elim!: option_relE simp: cref_rel_def in_br_conv)
        done
    qed
    done

  
  definition "backtrack1 A T \<equiv> do {
    ASSUME (finite T);
    FOREACH T (\<lambda>x A. RETURN (A(x:=None))) A
  }"
  
  lemma backtrack1_correct[THEN SPEC_trans, refine_vcg]: 
    "backtrack1 A T \<le> SPEC (\<lambda>r. r = backtrack A T)"
    unfolding backtrack1_def
    apply (refine_vcg FOREACH_rule[where I="\<lambda>it A'. A' = backtrack A (T-it)"])
    apply (vc_solve simp: backtrack_def)
    by (auto simp:  it_step_insert_iff restrict_map_def intro!: ext)
  
      
  definition (in -) abs_cr_register_ndj 
  :: "'a literal \<Rightarrow> 'id \<Rightarrow> ('a literal \<rightharpoonup> 'id list) \<Rightarrow> ('a literal \<rightharpoonup> 'id list)" 
  where "abs_cr_register_ndj l cid cr \<equiv> case cr l of 
    None \<Rightarrow> cr | Some s \<Rightarrow> cr(l \<mapsto> cid#s)"
      
      
  definition "register_clause1 cid cref RL \<equiv> doE {
      iterate_clause cref (\<lambda>_. True) (\<lambda>l RL. doE {
        ERETURN (abs_cr_register_ndj l cid RL)
      }) RL
    }"
  
  \<^cancel>\<open> XXX: Do we really need mbhd-insert?
      We iterate over literals of clause, which 
      should not contain duplicates!
  \<close>  
    
    
  definition "RL_upd cid C RL \<equiv> (\<lambda>l. case RL l of 
      None \<Rightarrow> None 
    | Some s \<Rightarrow> if l\<in>C then Some (insert cid s) else Some s)"
  
  lemma RL_upd_empty[simp]: "RL_upd cid {} RL = RL"
    by (auto simp: RL_upd_def split: option.split)
  
  lemma RL_upd_insert_eff: 
    "RL_upd cid C RL l = Some s 
    \<Longrightarrow> RL_upd cid (insert l C) RL = (RL_upd cid C RL)(l \<mapsto> insert cid s)"
    by (auto simp: RL_upd_def split: option.split if_split_asm intro!: ext)
  
  lemma RL_upd_insert_noeff: 
    "RL_upd cid C RL l = None \<Longrightarrow> RL_upd cid (insert l C) RL = RL_upd cid C RL"
    by (auto simp: RL_upd_def split: option.split if_split_asm intro!: ext)
  
  
  lemma register_clause1_correct[THEN ESPEC_trans, refine_vcg]: 
    assumes CR: "(cref,C)\<in>cref_rel"
    assumes RL: "(RLi,RL)\<in>Id \<rightarrow> \<langle>br set (\<lambda>_. True)\<rangle>option_rel"
    \<^cancel>\<open>assumes fresh_id: "cid \<notin> \<Union>ran RL"\<close>
    shows "register_clause1 cid cref RLi 
      \<le> ESPEC (\<lambda>_. False) 
          (\<lambda>RLi'. (RLi', RL_upd cid C RL) \<in> Id \<rightarrow> \<langle>br set (\<lambda>_. True)\<rangle>option_rel)"
  proof -      
    show ?thesis
      unfolding register_clause1_def abs_cr_register_ndj_def
      apply (refine_vcg 
          iterate_clause_rule[OF CR, where 
            I="\<lambda>C RLi'. (RLi', RL_upd cid C RL) 
                        \<in> Id \<rightarrow> \<langle>br set (\<lambda>_. True)\<rangle>option_rel"]
          )
      apply (vc_solve solve: asm_rl) 
      
      subgoal for l
        using fun_relD[OF RL IdI[of l]] by simp
      subgoal for C l RL l'
        apply1 (frule fun_relD[OF _ IdI[of "l"]])
        apply1 (frule fun_relD[OF _ IdI[of "l'"]])
        apply1 (erule option_relE; 
                simp add: RL_upd_insert_eff RL_upd_insert_noeff)
        applyS (auto simp: in_br_conv mbhd_insert_correct mbhd_insert_invar) []
        done  
      subgoal for RLi l'
        apply1 (drule fun_relD[OF _ IdI[of "l'"]])
        apply1 (erule set_rev_mp[OF _ option_rel_mono])
        applyS (auto simp: in_br_conv mbhd_invar_exit)
        done
      done
  qed    
  
  definition add_clause1 
    :: "id \<Rightarrow> 'it \<Rightarrow> ('it) clausemap1 \<Rightarrow> (_,('it) clausemap1) enres"  
    where "add_clause1 \<equiv> \<lambda>i cref (CM,RL). doE {
      let CM = CM(i \<mapsto> cref);
      RL \<leftarrow> register_clause1 i cref RL;
      ERETURN (CM,RL)
      }"

      
  lemma add_clause1_refine[refine]:
    "\<lbrakk> (ii,i)\<in>Id; (cref,C)\<in>cref_rel; (CMi,CM)\<in>clausemap1_rel \<rbrakk> \<Longrightarrow>
      add_clause1 ii cref CMi \<le>\<Down>\<^sub>E UNIV clausemap1_rel (add_clause i C CM)"
    unfolding add_clause1_def add_clause_def
    apply (cases CMi; cases CM; simp only: split)
    subgoal for _ RLi _ RL
      apply refine_vcg
      supply RELATESI[of "Id \<rightarrow> _", refine_dref_RELATES]
      supply RELATESI[of "br set (\<lambda>_. True)", refine_dref_RELATES]
      apply refine_dref_type
      applyS assumption
      applyS (erule fun_relD[rotated, where f=RLi and f'=RL]; 
              auto simp: clausemap1_rel_def)
      \<^cancel>\<open>applyS (auto simp: cm_ids_def)\<close>
      apply1 clarsimp subgoal for RLi' l
        apply (drule fun_relD[OF _ IdI[of "l"]])
        apply (cases "RLi' l"; cases "RL l"; simp)
        applyS (auto simp: RL_upd_def split: if_split_asm) []
        applyS (auto simp: RL_upd_def split: if_split_asm) []
        applyS (auto 
                  simp: RL_upd_def cref_rel_def in_br_conv 
                  split: if_split_asm)
        done
      subgoal
        apply (simp add: clausemap1_rel_def)
        apply parametricity
        by auto
      done
    done
  
    
  definition check_rup_proof1 
    :: "('it) state1 \<Rightarrow> 'it \<Rightarrow> (nat\<times>'prf) \<Rightarrow> (_,('it) state1 \<times> 'it \<times> (nat\<times>'prf)) enres" 
    where
    "check_rup_proof1 \<equiv> \<lambda>(CM,A) it prf. doE {
      (i,prf) \<leftarrow> parse_id prf;
      CHECK (i\<notin>cm_ids CM) (mkp_errNprf STR ''Duplicate ID'' i prf);
      (cref,(A,T),it) \<leftarrow> parse_check_blocked1 A it;

      ((A,T),prf) \<leftarrow> apply_units1_bt CM A T prf;
      (confl_id,prf) \<leftarrow> parse_id prf;
      confl \<leftarrow> resolve_id1 CM confl_id;
      check_conflict_clause1 prf A confl;
      CM \<leftarrow> add_clause1 i cref CM;
      A \<leftarrow> enres_lift (backtrack1 A T);
      ERETURN ((CM,A),it,prf)
    }"

    
  lemma cm1_rel_imp_eq_ids[simp]: 
    assumes "(cm1,cm)\<in>clausemap1_rel" 
    shows "cm_ids cm1 = cm_ids cm"
  proof -
    show ?thesis using assms   
      apply (rule_tac IdD)
      unfolding clausemap1_rel_def cm_ids_def
      apply parametricity  
      apply (force elim!: option_relE dest: fun_relD[OF _ IdI])
      done          
  qed
    
  lemma check_rup_proof1_refine[refine]: 
    assumes SR: "(si,s)\<in>state1_rel"
    assumes [simplified, simp]: "(iti,it)\<in>Id" "(prfi,prf)\<in>Id"
    shows "check_rup_proof1 si iti prfi
            \<le>\<Down>\<^sub>E UNIV (state1_rel \<times>\<^sub>r Id \<times>\<^sub>r Id) (check_rup_proof_bt s it prf)"
  proof -
    have REW: "ERETURN (i,CM, backtrack A T) = doE { 
      let A = backtrack A T;
      ERETURN (i,CM,A)}" for i CM A T
      by auto
    
    note [refine_dref_RELATES] = RELATESI[of clausemap1_rel]    
        
    show ?thesis
      unfolding check_rup_proof1_def check_rup_proof_bt_def
      unfolding REW
      using SR
      apply refine_rcg
      apply refine_dref_type
      apply (vc_solve)
      subgoal by (intro refine_dref_RELATES) \<^cancel>\<open> TODO: refine_dref_type should always try to discharge RELATES-goals, 
                                                even if they do not contain schematic vars \<close>
      subgoal by refine_vcg auto  
      done
  qed
  
  definition "check_rat_candidates_part1 CM reslit candidates A prf \<equiv>         
    check_candidates' candidates A prf (\<lambda>cand_id A prf. doE {
      cand \<leftarrow> resolve_id1 CM cand_id;

      (A,T2) \<leftarrow> and_not_C_excl A cand (neg_lit reslit);
      ((A,T2),prf) \<leftarrow> apply_units1_bt CM A T2 prf;
      (confl_id,prf) \<leftarrow> parse_id prf;
      confl \<leftarrow> resolve_id1 CM confl_id;
      check_conflict_clause1 prf A confl;
      A \<leftarrow> enres_lift (backtrack1 A T2);
      ERETURN (A,prf)
    })"
      
  definition check_rat_proof1 
    :: "('it) state1 \<Rightarrow> 'it \<Rightarrow> (nat \<times> 'prf) \<Rightarrow> (_,('it) state1 \<times> 'it \<times> (nat \<times> 'prf)) enres" 
    where
    "check_rat_proof1 \<equiv> \<lambda>(CM,A) it prf. doE {
      (reslit,prf) \<leftarrow> parse_prf_literal prf;
      CHECK (sem_lit' reslit A \<noteq> Some False) 
            (mkp_errprf STR ''Resolution literal is false'' prf);
      (i,prf) \<leftarrow> parse_id prf;
      CHECK (i\<notin>cm_ids CM) (mkp_errNprf STR ''Ids must be strictly increasing'' i prf);
      (cref,(A,T),it) \<leftarrow> parse_check_blocked1 A it;

      CHECK_monadic (lit_in_clause1 cref reslit) 
                    (mkp_errprf STR ''Resolution literal not in clause'' prf);
      ((A,T),prf) \<leftarrow> apply_units1_bt CM A T prf;
      candidates \<leftarrow> get_rat_candidates1 CM A reslit;
      (A,prf) \<leftarrow> check_rat_candidates_part1 CM reslit candidates A prf;
      CM \<leftarrow> add_clause1 i cref CM;
      A \<leftarrow> enres_lift (backtrack1 A T);
      ERETURN ((CM,A),it,prf)
    }"
  
  lemma check_rat_proof1_refine[refine]: 
    assumes SR: "(si,s)\<in>state1_rel"
    assumes [simplified, simp]: "(iti,it)\<in>Id" "(prfi,prf)\<in>Id"
    shows "check_rat_proof1 si iti prfi
            \<le>\<Down>\<^sub>E UNIV (state1_rel \<times>\<^sub>r Id \<times>\<^sub>r Id) (check_rat_proof_bt s it prf)"
  proof -
    have REW1: "ERETURN (i,CM, backtrack A T) = doE { 
      let A = backtrack A T;
      ERETURN (i,CM,A)}" for i CM A T
      by auto

    have REW2: "ERETURN (backtrack A T, it) = doE { 
      let A = backtrack A T;
      ERETURN (A,it)}" for A T it
      by auto
    
    show ?thesis
      unfolding check_rat_proof1_def check_rat_proof_bt_def 
                check_rat_candidates_part1_def
      unfolding REW1 REW2
      using SR
      apply refine_vcg
      supply RELATESI[of "Id \<rightarrow> Id", refine_dref_RELATES]
      apply refine_dref_type
      supply [[goals_limit=1]]
      apply (vc_solve solve: asm_rl RELATESI) \<^cancel>\<open> Takes its time ... \<close>
      done
  qed
  
  
  definition remove_id1 
    :: "id \<Rightarrow> ('cref) clausemap1 \<Rightarrow> (_,('cref) clausemap1) enres"
    where "remove_id1 \<equiv> \<lambda>i (CM,RL). ERETURN (CM(i:=None),RL)"
    
  lemma remove_id1_refine[refine]: 
    "\<lbrakk> (ii,i)\<in>Id; (CMi,CM)\<in>clausemap1_rel \<rbrakk> 
      \<Longrightarrow> remove_id1 ii CMi \<le>\<Down>\<^sub>E UNIV clausemap1_rel (remove_id i CM)"
    unfolding remove_id1_def remove_id_def
    by (auto 
        simp: pw_ele_iff refine_pw_simps clausemap1_rel_def 
        simp: in_br_conv restrict_map_def
        dest: fun_relD
        elim: option_relE
        split: prod.split
        )
  
  definition remove_ids1
      :: "('cref) clausemap1 \<Rightarrow> (nat \<times> 'prf) \<Rightarrow> (_,('cref) clausemap1 \<times> (nat \<times> 'prf)) enres"
    where    
    "remove_ids1 CM prf \<equiv> doE {
      (i,prf) \<leftarrow> parse_idZ prf;
      (CM,i,prf) \<leftarrow> EWHILET 
        (\<lambda>(_,i,_). i\<noteq>0) 
        (\<lambda>(CM,i,prf). doE {
          CM \<leftarrow> remove_id1 i CM;
          (i,prf) \<leftarrow> parse_idZ prf;
          ERETURN (CM,i,prf)
        }) (CM,i,prf);
      ERETURN (CM,prf)
  }"
      
  lemma remove_ids1_refine[refine]: 
    "\<lbrakk> (CMi,CM)\<in>clausemap1_rel; (prfi,prf)\<in>Id \<rbrakk> 
      \<Longrightarrow> remove_ids1 CMi prfi \<le>\<Down>\<^sub>E UNIV (clausemap1_rel \<times>\<^sub>r Id) (remove_ids CM prf)"
    unfolding remove_ids1_def remove_ids_def EWHILET_def \<^cancel>\<open> TODO: Register EWHILET \<le> EWHILEIT refine rule \<close>
    supply RELATESI[of clausemap1_rel, refine_dref_RELATES]
    apply refine_rcg
    apply refine_dref_type
    apply vc_solve
    done  
  
  definition check_item1 
    :: "('it) state1 \<Rightarrow> 'it \<Rightarrow> (nat \<times> 'prf) \<Rightarrow> (_,(('it) state1 \<times> 'it \<times> (nat \<times> 'prf)) option) enres"
    where "check_item1 \<equiv> \<lambda>(CM,A) it prf. doE {
      (ty,prf) \<leftarrow> parse_type prf;
      case ty of
        INVALID \<Rightarrow> THROW (mkp_err STR ''Invalid item'')
      | UNIT_PROP \<Rightarrow> doE {
          (A,prf) \<leftarrow> apply_units1 CM A prf;
          ERETURN (Some ((CM,A),it,prf))
        }
      | DELETION \<Rightarrow> doE {
          (CM,prf) \<leftarrow> remove_ids1 CM prf;
          ERETURN (Some ((CM,A),it,prf))
        }
      | RUP_LEMMA \<Rightarrow> doE {
          s \<leftarrow> check_rup_proof1 (CM,A) it prf;
          ERETURN (Some s)
        }
      | RAT_LEMMA \<Rightarrow> doE {
          s \<leftarrow> check_rat_proof1 (CM,A) it prf;
          ERETURN (Some s)
        }
      | CONFLICT \<Rightarrow> doE {
          (i,prf) \<leftarrow> parse_id prf;
          cref \<leftarrow> resolve_id1 CM i;
          check_conflict_clause1 prf A cref;
          ERETURN None
        }
      | RAT_COUNTS \<Rightarrow> THROW (mkp_errprf
            STR ''Not expecting rat-counts in the middle of proof'' prf)
    }"
    
    
  lemma check_item1_refine[refine]: 
    assumes SR: "(si,s)\<in>state1_rel"
    assumes [simplified, simp]: "(iti,it)\<in>Id" "(prfi,prf)\<in>Id"
    shows "check_item1 si iti prfi
            \<le>\<Down>\<^sub>E UNIV (\<langle>state1_rel \<times>\<^sub>r Id \<times>\<^sub>r Id\<rangle>option_rel) (check_item_bt s it prf)"
    unfolding check_item1_def check_item_bt_def
    apply refine_rcg
    using SR
    apply refine_dref_type
    applyS simp
    apply (split item_type.split; intro allI impI conjI; clarsimp)
    apply ((refine_rcg, refine_dref_type?); auto; fail)+
    done

  lemma check_item1_deforest: "check_item1 = (\<lambda>(CM,A) it prf. doE {
      (ty,prf) \<leftarrow> parse_prf prf;
      if ty=1 then doE {
          (A,prf) \<leftarrow> apply_units1 CM A prf;
          ERETURN (Some ((CM,A),it,prf))
        }
      else if ty=2 then doE {
          (CM,prf) \<leftarrow> remove_ids1 CM prf;
          ERETURN (Some ((CM,A),it,prf))
        }
      else if ty=3 then doE {
          s \<leftarrow> check_rup_proof1 (CM,A) it prf;
          ERETURN (Some s)
        }
      else if ty=4 then doE {
          s \<leftarrow> check_rat_proof1 (CM,A) it prf;
          ERETURN (Some s)
        }
      else if ty=5 then doE {
          (i,prf) \<leftarrow> parse_id prf;
          cref \<leftarrow> resolve_id1 CM i;
          check_conflict_clause1 prf A cref;
          ERETURN None
        }
      else if ty=6 then 
        THROW (mkp_errprf STR ''Not expecting rat-counts in the middle of proof'' prf)
      else 
        THROW (mkp_errIprf STR ''Invalid item type'' ty prf)
    })"
    unfolding check_item1_def parse_type_def
    \<^cancel>\<open> Hand-tuned proof to avoid explosion \<close>  
    apply (intro ext)  
    apply (simp split: prod.split)
    apply (intro allI impI)  
    apply (fo_rule fun_cong arg_cong)+
    apply (intro ext)  
    apply (simp split: prod.split)
    done  
      
    
  definition (in -) cm_empty1 :: "('cref) clausemap1" 
    where "cm_empty1 \<equiv> (Map.empty, Map.empty)"
  lemma cm_empty_refine[refine]: "(cm_empty1, cm_empty) \<in> clausemap1_rel"  
    unfolding cm_empty1_def cm_empty_def clausemap1_rel_def
    by auto
  
  definition "is_syn_taut1 cref A \<equiv> doE {
    EASSERT (A = Map.empty);
    (t,A) \<leftarrow> iterate_clause cref (\<lambda>(t,A). \<not>t) (\<lambda>l (t,A). doE {
      if (sem_lit' l A = Some False) then ERETURN (True,A)
      else if sem_lit' l A = Some True then ERETURN (False,A) \<^cancel>\<open> DUP literal. Perhaps check for it? \<close>
      else doE {
        EASSERT (sem_lit' l A = None);
        ERETURN (False,assign_lit A l)
      }
    }) (False,A);

    \<^cancel>\<open> Iterate again over clause to reset assignment \<close>
    A \<leftarrow> iterate_clause cref (\<lambda>_. True) (\<lambda>l A. doE {
      let A = A(var_of_lit l := None);
      ERETURN A
    }) A;

    ERETURN (t,A)
  }"

  lemma is_syn_taut1_correct[THEN ESPEC_trans, refine_vcg]:
    assumes CR: "(cref,C)\<in>cref_rel"
    assumes [simp]: "A = Map.empty"  
    shows "is_syn_taut1 cref A 
            \<le> ESPEC (\<lambda>_. False) (\<lambda>(t,A). (t \<longleftrightarrow> is_syn_taut C) \<and> A=Map.empty)"
  proof -
    show ?thesis
      unfolding is_syn_taut1_def 
      apply (refine_vcg
        iterate_clause_rule[OF CR, where I="\<lambda>C (t,A). 
            (t \<longrightarrow> is_syn_taut C) 
          \<and> (\<not>t \<longrightarrow> (\<forall>l. sem_lit' l A = Some True \<longleftrightarrow> l\<in>C)) 
          \<and> dom A \<subseteq> var_of_lit`C"]
        iterate_clause_rule[OF CR, 
          where I="\<lambda>C' A. (dom A \<subseteq> var_of_lit`(C - C'))"]  
       )
      apply (vc_solve simp: not_Some_bool_if)
      apply (auto)
      apply (auto simp: is_syn_taut_def) []
      apply (auto simp: sem_lit'_assign_conv split: if_splits) []
      apply (force simp: sem_lit'_assign_conv split: if_splits) []
      subgoal for _ l by (case_tac l; auto split: if_splits)
      subgoal premises prems for _ A
      proof -
        from prems have 
          SL: "\<forall>l. sem_lit' l A = Some True \<longleftrightarrow> l\<in>C" and
          TAUT: "is_syn_taut C" 
          by auto
        
        from TAUT obtain l where "l\<in>C" "neg_lit l \<in> C" 
          by (auto simp: is_syn_taut_conv)
        with SL 
        have "sem_lit' l A = Some True" "sem_lit' (neg_lit l) A = Some True" 
          by (auto simp del: sem_neg_lit')
        thus False by simp
      qed
      subgoal by fastforce
      subgoal by (fastforce simp: is_syn_taut_def)
      done
  qed
  
\<^cancel>\<open>    
  definition read_cnf1 
    :: "'it list \<Rightarrow> ('it) clausemap1 \<Rightarrow> (_,('it) clausemap1 \<times> nat) enres" 
    where "read_cnf1 L CM \<equiv> doE {
      (CM,next_id,A) \<leftarrow> enfoldli L (\<lambda>_. True) (\<lambda>C (CM,i,A). doE {
        (ist,A) \<leftarrow> is_syn_taut1 C A;
        if ist then 
          ERETURN (CM,i+1,A)
        else doE {
          CM \<leftarrow> add_clause1 i C CM;
          ERETURN (CM,i+1,A)
        }
      }) (CM,1,Map.empty);
      ERETURN (CM, next_id - 1)
    }"

  lemma read_cnf1_refine[refine]: 
    assumes [simp]: "(Fi,F)\<in>\<langle>cref_rel\<rangle>list_rel"
    assumes [simp]: "(CMi,CM)\<in>clausemap1_rel"
    shows "read_cnf1 Fi CMi 
            \<le> \<Down>\<^sub>E UNIV (clausemap1_rel \<times>\<^sub>r nat_rel) (read_cnf F CM)"
  proof -
    have REW: "(If (is_syn_taut C) t e) = (let b=is_syn_taut C in If b t e)" 
      for C t e 
      by auto
    
    let ?rel = "{ ((cmi,ii,A),(cm,i)). (cmi,cm)\<in>clausemap1_rel 
                                      \<and> ii=i \<and> A=Map.empty}"
    let ?rel2 = "{ ((bi,A),b). bi=b \<and> A=Map.empty}"
    
    show ?thesis
      unfolding read_cnf1_def read_cnf_def
      supply RELATESI[of clausemap1_rel, refine_dref_RELATES]
      supply RELATESI[of ?rel, refine_dref_RELATES]
      supply RELATESI[of ?rel2, refine_dref_RELATES]
      supply RELATESI[of cref_rel, refine_dref_RELATES]
      apply (rewrite REW)
      apply (refine_vcg)
      apply refine_dref_type
      apply (auto simp: cm_empty_refine)
      done
  qed
\<close>  

  definition read_cnf_new1 
    :: "'it \<Rightarrow> 'it \<Rightarrow> 'it clausemap1 \<Rightarrow> (_, 'it clausemap1) enres"    
    where "read_cnf_new1 itE it CM \<equiv> doE {
      (CM,next_id,A) \<leftarrow> tok_fold itE it (\<lambda>it (CM,next_id,A). doE {
        (it',(t,A)) \<leftarrow> read_clause_check_taut itE it A;
        if t then ERETURN (it', (CM,next_id+1,A))
        else doE {
          EASSERT (\<exists>l it'. lz_string litZ it l it');
          let C = it;
          CM \<leftarrow> add_clause1 next_id C CM;
          ERETURN (it',(CM,next_id+1,A))
        }
      }) (CM,1,Map.empty);
      ERETURN (CM)
    }"
    
  lemma read_cnf_new1_refine[refine]:  
    assumes [simplified,simp]: "(F_begini, F_begin)\<in>Id" "(F_endi,F_end)\<in>Id"
    assumes [simp]: "(CMi,CM)\<in>clausemap1_rel"
    shows "read_cnf_new1 F_endi F_begini CMi 
            \<le> \<Down>\<^sub>E UNIV (clausemap1_rel) 
            (read_cnf_new F_end F_begin CM)"
    unfolding read_cnf_new1_def read_cnf_new_def
    apply refine_rcg
    supply RELATESI[of clausemap1_rel, refine_dref_RELATES]
    apply refine_dref_type  
    apply vc_solve  
    applyS auto  
    subgoal unfolding cref_rel_def by auto
    done    
    
  definition cm_init_lit1 
    :: "var literal \<Rightarrow> ('it) clausemap1 \<Rightarrow> (_,('it) clausemap1) enres"
    where "cm_init_lit1 \<equiv> \<lambda>l (CM,RL). ERETURN (CM,RL(l \<mapsto> []))"
    
  definition "init_rat_counts1 prf \<equiv> doE { 
    (ty,prf) \<leftarrow> parse_type prf;
    CHECK (ty = RAT_COUNTS) (mkp_errprf STR ''Expected RAT counts item'' prf);

    (l,prf) \<leftarrow> parse_prf_literalZ prf;
    (CM,_,prf) \<leftarrow> EWHILET (\<lambda>(CM,l,prf). l\<noteq>None) (\<lambda>(CM,l,prf). doE {
      EASSERT (l\<noteq>None);
      let l = the l;
      (_,prf) \<leftarrow> parse_prf prf;
      
      let l = neg_lit l;
      CM \<leftarrow> cm_init_lit1 l CM;
      
      (l,prf) \<leftarrow> parse_prf_literalZ prf;
      ERETURN (CM,l,prf)
    }) (cm_empty1,l,prf);
  
    ERETURN (CM,prf)
  }"
    
  lemma init_rat_counts1_refine[refine]: 
    assumes [simplified,simp]: "(prfi,prf)\<in>Id"
    shows "init_rat_counts1 prfi \<le>\<Down>\<^sub>E UNIV (clausemap1_rel \<times>\<^sub>r Id) (init_rat_counts prf)"  
    unfolding init_rat_counts1_def init_rat_counts_def 
              cm_init_lit_def cm_init_lit1_def
    apply refine_rcg
    supply RELATESI[of clausemap1_rel, refine_dref_RELATES]
    apply refine_dref_type  
    apply (vc_solve simp: cm_empty_refine)
    subgoal by (auto simp: clausemap1_rel_def in_br_conv dest!: fun_relD)
    done
      
  lemma init_rat_counts1_deforest: "init_rat_counts1 prf = doE { 
    (ty,prf) \<leftarrow> parse_prf prf;
    CHECK (ty = 1 \<or> ty = 2 \<or> ty = 3 \<or> ty = 4 \<or> ty = 5 \<or> ty = 6) 
          (mkp_errIprf STR ''Invalid item type'' ty prf);
    CHECK (ty = 6) (mkp_errprf STR ''Expected RAT counts item'' prf);
    (l,prf) \<leftarrow> parse_prf_literalZ prf;
    (CM,l,prf) \<leftarrow> EWHILET 
      (\<lambda>(CM,l,prf). l\<noteq>None) 
      (\<lambda>(CM,l,prf). doE {
        EASSERT (l\<noteq>None);
        let l = the l;

        (_,prf) \<leftarrow> parse_prf prf; 
        let l = neg_lit l;
        CM \<leftarrow> cm_init_lit1 l CM;

        (l,prf) \<leftarrow> parse_prf_literalZ prf;
        ERETURN (CM,l,prf)
      }) (cm_empty1,l,prf);
    ERETURN (CM,prf)
  }"
    unfolding init_rat_counts1_def parse_type_def
    apply (simp split: prod.split)
    apply (fo_rule fun_cong arg_cong)+
    apply (intro ext)  
    apply (simp split: prod.split)
    done  
      
      
  definition "verify_unsat1 F_begin F_end it prf \<equiv> doE {

    EASSERT (it_invar it);

    (CM,prf) \<leftarrow> init_rat_counts1 prf;

    CM \<leftarrow> read_cnf_new1 F_end F_begin CM;
  
    let s = (CM,Map.empty);

    EWHILEIT 
      (\<lambda>Some (_,it,_) \<Rightarrow> it_invar it | None \<Rightarrow> True) 
      (\<lambda>s. s\<noteq>None) 
      (\<lambda>s. doE {
        EASSERT (s\<noteq>None);
        let (s,it,prf) = the s;
    
        EASSERT (it_invar it); 
    
        check_item1 s it prf
      }) (Some (s,it,prf));
    ERETURN ()  
    \<^cancel>\<open>CHECK (is_None s) (mkp_err ''Proof did not contain conflict declaration'')\<close>
  }"
  
  lemma verify_unsat1_refine[refine]: 
    "\<lbrakk> (F_begini,F_begin)\<in>Id; (F_endi,F_end)\<in>Id; (iti,it)\<in>Id; (prfi,prf)\<in>Id \<rbrakk> 
      \<Longrightarrow> verify_unsat1 F_begini F_endi iti prfi
          \<le>\<Down>\<^sub>E UNIV Id (verify_unsat_bt F_begin F_end it prf)"
    unfolding verify_unsat1_def verify_unsat_bt_def
    apply refine_rcg
    supply RELATESI[of state1_rel, refine_dref_RELATES]
    apply (auto elim: option_relE)
    done
  
end

subsection \<open>Refinement 2\<close>
\<^cancel>\<open>
  id \<rightarrow> nat (already done for verify_unsat1)
  (id \<rightharpoonup> 'a) \<rightarrow> 'a option array, dynamic resizing (iam!?)

  literal \<rightarrow> int \<noteq> 0
  (literal \<rightharpoonup> 'a) \<rightarrow> 'a array, indexing: 2*|l| + sgn l. Array uses dynamic resizing. (based on iam!?)

  assignment: variable \<rightharpoonup> bool, (iam)
  
  candidate list: stick to list, or use array-list (with reversed order) 

  clausedb \<rightarrow> array, which also contains proof items. size N

  cref \<rightarrow> nat < N
  proof-item \<rightarrow> nat < N (reference into array)
\<close>


subsubsection \<open>Getting Out of Exception Monad\<close>

context unsat_input
begin
  lemmas [enres_inline] = parse_id_def parse_idZ_def parse_prf_literal_def parse_prf_literalZ_def

  synth_definition parse_prf_bd is [enres_unfolds]: "parse_prf prf = \<hole>"  
    apply (rule CNV_eqD)
    unfolding parse_prf_def
    apply opt_enres_unfold
    apply (rule CNV_I)
    done
    
  \<^cancel>\<open>synth_definition parse_type_bd is [enres_unfolds]: "parse_type prf = \<hole>"  
    apply (rule CNV_eqD)
    unfolding parse_type_def
    apply opt_enres_unfold
    apply (rule CNV_I)
    done\<close>
  
  synth_definition check_unit_clause1_bd 
    is [enres_unfolds]: "check_unit_clause1 A cref = \<hole>"
    apply (rule CNV_eqD)
    unfolding check_unit_clause1_def iterate_clause_def \<^cancel>\<open>iterate_lz_def\<close>
    apply opt_enres_unfold
    apply (rule CNV_I)
    done

  \<comment> \<open>Optimization to reduce map lookups\<close>
  lemma resolve_id1_alt: "resolve_id1 = (\<lambda>(CM,_) i. doE {
      let x = CM i;
      if (x=None) then THROW (mkp_errN STR ''Invalid clause id'' i)
      else ERETURN (the x)
    })"
    unfolding resolve_id1_def
    apply (intro ext)
    apply (auto simp: pw_eeq_iff refine_pw_simps Let_def split: if_split_asm)
    done
  
  synth_definition resolve_id1_bd is [enres_unfolds]: "resolve_id1 CM cid = \<hole>"
    apply (rule CNV_eqD)
    unfolding resolve_id1_alt
    apply opt_enres_unfold
    apply (rule CNV_I)
    done
  
  synth_definition apply_unit1_bt_bd 
    is [enres_unfolds]: "apply_unit1_bt i CM A T = \<hole>"
    apply (rule CNV_eqD)
    unfolding apply_unit1_bt_def assign_lit_bt_def
    apply opt_enres_unfold
    apply (rule CNV_I)
    done
  
  synth_definition apply_units1_bt_bd 
    is [enres_unfolds]: "apply_units1_bt CM A T units = \<hole>"
    apply (rule CNV_eqD)
    unfolding apply_units1_bt_def
    apply opt_enres_unfold
    apply (rule CNV_I)
    done
  

  synth_definition apply_unit1_bd is [enres_unfolds]: "apply_unit1 i CM A = \<hole>"
    apply (rule CNV_eqD)
    unfolding apply_unit1_def
    apply opt_enres_unfold
    apply (rule CNV_I)
    done
  
  synth_definition apply_units1_bd 
    is [enres_unfolds]: "apply_units1 CM A units = \<hole>"
    apply (rule CNV_eqD)
    unfolding apply_units1_def
    apply opt_enres_unfold
    apply (rule CNV_I)
    done
  
  synth_definition remove_ids1_bd 
    is [enres_unfolds]: "remove_ids1 CM prf = \<hole>"
    apply (rule CNV_eqD)
    unfolding remove_ids1_def remove_id1_def
    apply opt_enres_unfold
    apply (rule CNV_I)
    done
      
  synth_definition parse_check_blocked1_bd 
    is [enres_unfolds]: "parse_check_blocked1 A cref = \<hole>"
    apply (rule CNV_eqD)
    unfolding parse_check_blocked1_def parse_check_clause_def \<^cancel>\<open>parse_lz_def\<close>
    apply opt_enres_unfold
    apply (rule CNV_I)
    done
  
  synth_definition check_conflict_clause1_bd 
    is [enres_unfolds]: "check_conflict_clause1 prf\<^sub>0 A cref = \<hole>"
    apply (rule CNV_eqD)
    unfolding check_conflict_clause1_def iterate_clause_def \<^cancel>\<open>iterate_lz_def\<close>
    apply opt_enres_unfold
    apply (rule CNV_I)
    done
  
  synth_definition and_not_C_excl_bd 
    is [enres_breakdown]: "and_not_C_excl A cref exl = enres_lift \<hole>"
    unfolding and_not_C_excl_def iterate_clause_def \<^cancel>\<open>iterate_lz_def \<close>
    by opt_enres_unfold
  
  synth_definition lit_in_clause_and_not_true_bd 
    is [enres_breakdown]: "lit_in_clause_and_not_true A cref lc = enres_lift \<hole>"
    unfolding lit_in_clause_and_not_true_def iterate_clause_def \<^cancel>\<open>iterate_lz_def \<close>
    by opt_enres_unfold

  synth_definition lit_in_clause_bd 
    is [enres_breakdown]: "lit_in_clause1 cref lc = enres_lift \<hole>"
    unfolding lit_in_clause1_def iterate_clause_def \<^cancel>\<open>iterate_lz_def\<close> 
    by opt_enres_unfold
      
      
  synth_definition get_rat_candidates1_bd 
    is [enres_unfolds]: "get_rat_candidates1 CM A l = \<hole>"
    apply (rule CNV_eqD)
    unfolding get_rat_candidates1_def 
    apply opt_enres_unfold
    apply (rule CNV_I)
    done
      
  synth_definition add_clause1_bd 
    is [enres_breakdown]: "add_clause1 i it CM = enres_lift \<hole>"
    unfolding add_clause1_def register_clause1_def iterate_clause_def \<^cancel>\<open>iterate_lz_def\<close>
    by opt_enres_unfold
      
  synth_definition check_rup_proof1_bd 
    is [enres_unfolds]: "check_rup_proof1 s it prf = \<hole>"
    apply (rule CNV_eqD)
    unfolding check_rup_proof1_def 
    apply opt_enres_unfold
    apply (rule CNV_I)
    done

  term check_rat_candidates_part1   
  synth_definition check_rat_candidates_part1_bd 
    is [enres_unfolds]: 
        "check_rat_candidates_part1 CM reslit candidates A prf = \<hole>"
    apply (rule CNV_eqD)
    unfolding check_rat_candidates_part1_def 
              check_candidates'_def parse_skip_listZ_def \<^cancel>\<open>parse_lz_def\<close>
    apply opt_enres_unfold
    apply (rule CNV_I)
    done
      
  synth_definition check_rat_proof1_bd 
    is [enres_unfolds]: "check_rat_proof1 s it prf = \<hole>"
    apply (rule CNV_eqD)
    unfolding check_rat_proof1_def 
    apply opt_enres_unfold
    apply (rule CNV_I)
    done

  synth_definition check_item1_bd is [enres_unfolds]: "check_item1 s it prf = \<hole>"
    apply (rule CNV_eqD)
    unfolding check_item1_deforest
    apply opt_enres_unfold
    apply (rule CNV_I)
    done
      
  synth_definition is_syn_taut1_bd 
    is [enres_breakdown]: "is_syn_taut1 cref A = enres_lift \<hole>"    
    unfolding is_syn_taut1_def iterate_clause_def \<^cancel>\<open>iterate_lz_def\<close>
    by opt_enres_unfold
      
\<^cancel>\<open>  synth_definition read_cnf1_bd 
    is [enres_breakdown]: "read_cnf1 F CM = enres_lift \<hole>"
    unfolding read_cnf1_def
    by opt_enres_unfold
\<close>

  synth_definition read_clause_check_taut_bd 
    is [enres_unfolds]: "read_clause_check_taut F_end F_begin A = \<hole>"    
    apply (rule CNV_eqD)
    unfolding read_clause_check_taut_def \<^cancel>\<open>parse_lz_def iterate_lz_def\<close>
    apply opt_enres_unfold
    apply (rule CNV_I)
    done  

  synth_definition read_cnf_new1_bd 
    is [enres_unfolds]: "read_cnf_new1 F_begin F_end CM = \<hole>"
    apply (rule CNV_eqD)
    unfolding read_cnf_new1_def tok_fold_def
    apply opt_enres_unfold
    apply (rule CNV_I)
    done  
      
      
  synth_definition init_rat_counts1_bd 
    is [enres_unfolds]: "init_rat_counts1 prf = \<hole>"   
    apply (rule CNV_eqD)
    unfolding init_rat_counts1_deforest cm_init_lit1_def
    apply opt_enres_unfold
    apply (rule CNV_I)
    done  
      
  \<^cancel>\<open>synth_definition goto_next_item_bd 
    is [enres_unfolds]: "goto_next_item it = \<hole>"   
    apply (rule CNV_eqD)
    unfolding goto_next_item_def
    apply opt_enres_unfold
    apply (rule CNV_I)
    done  
  \<close>
      
  synth_definition verify_unsat1_bd 
    is [enres_unfolds]: "verify_unsat1 F_begin F_end it prf = \<hole>"
    apply (rule CNV_eqD)
    unfolding verify_unsat1_def
    apply opt_enres_unfold
    apply (rule CNV_I)
    done  
      
      
end

subsubsection \<open>Instantiating Input Locale\<close>  
  
locale GRAT_def_loc = DB2_def_loc +
  fixes prf_next :: "'prf \<Rightarrow> int \<times> 'prf"
  
locale GRAT_loc = DB2_loc DB frml_end + GRAT_def_loc DB frml_end prf_next
  for DB frml_end and prf_next :: "'prf \<Rightarrow> int \<times> 'prf"

    
context GRAT_loc
begin
  sublocale unsat_input liti.next liti.peek liti.end liti.I prf_next
    apply unfold_locales
    done 
    
end
  
subsubsection \<open>Extraction from Locale\<close>  
  
named_theorems extrloc_unfolds  

concrete_definition (in GRAT_loc) parse_prf2_loc 
  uses parse_prf_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) parse_prf2_loc.refine[extrloc_unfolds]
concrete_definition parse_prf2 
  uses GRAT_loc.parse_prf2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) parse_prf2.refine[OF GRAT_loc_axioms, extrloc_unfolds]
  
  
concrete_definition (in GRAT_loc) parse_check_blocked2_loc 
  uses parse_check_blocked1_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) parse_check_blocked2_loc.refine[extrloc_unfolds]
concrete_definition parse_check_blocked2 
  uses GRAT_loc.parse_check_blocked2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) parse_check_blocked2.refine[OF GRAT_loc_axioms, extrloc_unfolds]

concrete_definition (in GRAT_loc) check_unit_clause2_loc 
  uses check_unit_clause1_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) check_unit_clause2_loc.refine[extrloc_unfolds]
concrete_definition check_unit_clause2 uses GRAT_loc.check_unit_clause2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) check_unit_clause2.refine[OF GRAT_loc_axioms, extrloc_unfolds]

concrete_definition (in GRAT_loc) resolve_id2_loc 
  uses resolve_id1_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) resolve_id2_loc.refine[extrloc_unfolds]
concrete_definition resolve_id2 uses GRAT_loc.resolve_id2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) resolve_id2.refine[OF GRAT_loc_axioms, extrloc_unfolds]

concrete_definition (in GRAT_loc) apply_units2_loc 
  uses apply_units1_bd_def[unfolded apply_unit1_bd_def extrloc_unfolds]
declare (in GRAT_loc) apply_units2_loc.refine[extrloc_unfolds]
concrete_definition apply_units2 uses GRAT_loc.apply_units2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) apply_units2.refine[OF GRAT_loc_axioms, extrloc_unfolds]
  
concrete_definition (in GRAT_loc) apply_units2_bt_loc 
  uses apply_units1_bt_bd_def[unfolded apply_unit1_bt_bd_def extrloc_unfolds]
declare (in GRAT_loc) apply_units2_bt_loc.refine[extrloc_unfolds]
concrete_definition apply_units2_bt uses GRAT_loc.apply_units2_bt_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) apply_units2_bt.refine[OF GRAT_loc_axioms, extrloc_unfolds]

concrete_definition (in GRAT_loc) remove_ids2_loc 
  uses remove_ids1_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) remove_ids2_loc.refine[extrloc_unfolds]
concrete_definition remove_ids2 uses GRAT_loc.remove_ids2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) remove_ids2.refine[OF GRAT_loc_axioms, extrloc_unfolds]
  
concrete_definition (in GRAT_loc) check_conflict_clause2_loc 
  uses check_conflict_clause1_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) check_conflict_clause2_loc.refine[extrloc_unfolds]
concrete_definition check_conflict_clause2 uses GRAT_loc.check_conflict_clause2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) check_conflict_clause2.refine[OF GRAT_loc_axioms, extrloc_unfolds]

  
concrete_definition (in GRAT_loc) and_not_C_excl2_loc 
  uses and_not_C_excl_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) and_not_C_excl2_loc.refine[extrloc_unfolds]
concrete_definition and_not_C_excl2 uses GRAT_loc.and_not_C_excl2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) and_not_C_excl2.refine[OF GRAT_loc_axioms, extrloc_unfolds]

  
concrete_definition (in GRAT_loc) lit_in_clause_and_not_true2_loc 
  uses lit_in_clause_and_not_true_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) lit_in_clause_and_not_true2_loc.refine[extrloc_unfolds]
concrete_definition lit_in_clause_and_not_true2 uses GRAT_loc.lit_in_clause_and_not_true2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) lit_in_clause_and_not_true2.refine[OF GRAT_loc_axioms, extrloc_unfolds]

concrete_definition (in GRAT_loc) get_rat_candidates2_loc 
  uses get_rat_candidates1_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) get_rat_candidates2_loc.refine[extrloc_unfolds]
concrete_definition get_rat_candidates2 uses GRAT_loc.get_rat_candidates2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) get_rat_candidates2.refine[OF GRAT_loc_axioms, extrloc_unfolds]

concrete_definition (in GRAT_loc) backtrack2_loc 
  uses backtrack1_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) backtrack2_loc.refine[extrloc_unfolds]
concrete_definition backtrack2 uses GRAT_loc.backtrack2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) backtrack2.refine[OF GRAT_loc_axioms, extrloc_unfolds]

concrete_definition (in GRAT_loc) add_clause2_loc 
  uses add_clause1_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) add_clause2_loc.refine[extrloc_unfolds]
concrete_definition add_clause2 uses GRAT_loc.add_clause2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) add_clause2.refine[OF GRAT_loc_axioms, extrloc_unfolds]

concrete_definition (in GRAT_loc) check_rup_proof2_loc 
  uses check_rup_proof1_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) check_rup_proof2_loc.refine[extrloc_unfolds]
concrete_definition check_rup_proof2 uses GRAT_loc.check_rup_proof2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) check_rup_proof2.refine[OF GRAT_loc_axioms, extrloc_unfolds]

concrete_definition (in GRAT_loc) lit_in_clause2_loc 
  uses lit_in_clause_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) lit_in_clause2_loc.refine[extrloc_unfolds]
concrete_definition lit_in_clause2 uses GRAT_loc.lit_in_clause2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) lit_in_clause2.refine[OF GRAT_loc_axioms, extrloc_unfolds]

  
concrete_definition (in GRAT_loc) check_rat_candidates_part2_loc 
  uses check_rat_candidates_part1_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) check_rat_candidates_part2_loc.refine[extrloc_unfolds]
concrete_definition check_rat_candidates_part2 uses GRAT_loc.check_rat_candidates_part2_loc_def[unfolded extrloc_unfolds]
declare(in GRAT_loc)  check_rat_candidates_part2.refine[OF GRAT_loc_axioms, extrloc_unfolds]
  
concrete_definition (in GRAT_loc) check_rat_proof2_loc 
  uses check_rat_proof1_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) check_rat_proof2_loc.refine[extrloc_unfolds]
concrete_definition check_rat_proof2 uses GRAT_loc.check_rat_proof2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) check_rat_proof2.refine[OF GRAT_loc_axioms, extrloc_unfolds]

concrete_definition (in GRAT_loc) check_item2_loc 
  uses check_item1_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) check_item2_loc.refine[extrloc_unfolds]
concrete_definition check_item2 uses GRAT_loc.check_item2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) check_item2.refine[OF GRAT_loc_axioms, extrloc_unfolds]

concrete_definition (in GRAT_loc) is_syn_taut2_loc 
  uses is_syn_taut1_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) is_syn_taut2_loc.refine[extrloc_unfolds]
concrete_definition is_syn_taut2 uses GRAT_loc.is_syn_taut2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) is_syn_taut2.refine[OF GRAT_loc_axioms, extrloc_unfolds]

\<^cancel>\<open>  
concrete_definition (in GRAT_loc) read_cnf2_loc 
  uses read_cnf1_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) read_cnf2_loc.refine[extrloc_unfolds]
concrete_definition read_cnf2 uses GRAT_loc.read_cnf2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) read_cnf2.refine[OF GRAT_loc_axioms, extrloc_unfolds]
\<close>

concrete_definition (in GRAT_loc) read_clause_check_taut2_loc 
  uses read_clause_check_taut_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) read_clause_check_taut2_loc.refine[extrloc_unfolds]
concrete_definition read_clause_check_taut2 uses GRAT_loc.read_clause_check_taut2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) read_clause_check_taut2.refine[OF GRAT_loc_axioms, extrloc_unfolds]
  
concrete_definition (in GRAT_loc) read_cnf_new2_loc 
  uses read_cnf_new1_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) read_cnf_new2_loc.refine[extrloc_unfolds]
concrete_definition read_cnf_new2 uses GRAT_loc.read_cnf_new2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) read_cnf_new2.refine[OF GRAT_loc_axioms, extrloc_unfolds]
  
\<^cancel>\<open>concrete_definition (in GRAT_loc) goto_next_item2_loc 
  uses goto_next_item_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) goto_next_item2_loc.refine[extrloc_unfolds]
concrete_definition goto_next_item2 uses GRAT_loc.goto_next_item2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) goto_next_item2.refine[OF GRAT_loc_axioms, extrloc_unfolds]
\<close>

concrete_definition (in GRAT_loc) init_rat_counts2_loc 
  uses init_rat_counts1_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) init_rat_counts2_loc.refine[extrloc_unfolds]
concrete_definition init_rat_counts2 uses GRAT_loc.init_rat_counts2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) init_rat_counts2.refine[OF GRAT_loc_axioms, extrloc_unfolds]
 
  
concrete_definition (in GRAT_loc) verify_unsat2_loc 
  uses verify_unsat1_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) verify_unsat2_loc.refine[extrloc_unfolds]
concrete_definition verify_unsat2 uses GRAT_loc.verify_unsat2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) verify_unsat2.refine[OF GRAT_loc_axioms, extrloc_unfolds]

  
\<^cancel>\<open>  
concrete_definition (in GRAT_loc) XXX2_loc 
  uses XXX1_bd_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) XXX2_loc.refine[extrloc_unfolds]
concrete_definition XXX2 uses GRAT_loc.XXX2_loc_def[unfolded extrloc_unfolds]
declare (in GRAT_loc) XXX2.refine[OF GRAT_loc_axioms, extrloc_unfolds]
\<close>  

subsubsection \<open>Synthesis of Imperative Code\<close>  

definition "creg_register_ndj l cid cr \<equiv> do {
  x \<leftarrow> array_get_dyn None cr (int_encode l);
  case x of
    None \<Rightarrow> return cr
  | Some s \<Rightarrow> array_set_dyn None cr (int_encode l) (Some (cid#s))
}"
  
lemma creg_register_ndj_rule[sep_heap_rules]: 
  "\<lbrakk> (i,l) \<in> lit_rel \<rbrakk> 
  \<Longrightarrow> <is_creg cr a> 
        creg_register_ndj i cid a 
      <is_creg (abs_cr_register_ndj l cid cr)>\<^sub>t"
  unfolding creg_register_ndj_def is_creg_def abs_cr_register_ndj_def
  by (sep_auto intro!: ext simp: lit_rel_def in_br_conv int_encode_eq)

lemma creg_register_hnr[sepref_fr_rules]: 
  "(uncurry2 creg_register_ndj, uncurry2 (RETURN ooo abs_cr_register_ndj)) 
    \<in> (pure lit_rel)\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a is_creg\<^sup>d \<rightarrow>\<^sub>a is_creg"
  unfolding list_assn_pure_conv option_assn_pure_conv
  apply sepref_to_hoare
  apply sep_auto
  done
  
sepref_register "abs_cr_register_ndj :: nat literal \<Rightarrow> nat \<Rightarrow> _" 
  :: "nat literal \<Rightarrow> nat \<Rightarrow> (nat literal,nat list) i_map 
      \<Rightarrow> (nat literal,nat list) i_map"

    
    
context GRAT_def_loc 
begin  
  lemma pr_next_hnr[sepref_import_param]: "(prf_next,prf_next) \<in> Id \<rightarrow> Id \<times>\<^sub>r Id"
    by auto
    
  definition prfi_assn :: "nat \<times> 'prf \<Rightarrow> _" where "prfi_assn \<equiv> id_assn"

  definition prfn_assn :: "('prf \<Rightarrow> int \<times> 'prf) \<Rightarrow> _" where "prfn_assn \<equiv> id_assn"

  abbreviation "errorp_assn 
    \<equiv> (id_assn :: String.literal \<Rightarrow> _) \<times>\<^sub>a option_assn int_assn \<times>\<^sub>a option_assn prfi_assn"
      
      
  lemma prfi_assn_pure[safe_constraint_rules]: "is_pure prfi_assn" by (auto simp: prfi_assn_def)
    
  term prf_next
    
end
  
sepref_decl_intf 'prf i_prfi is "nat \<times> 'prf"
sepref_decl_intf 'prf i_prfn is "'prf \<Rightarrow> int \<times> 'prf"

context
  fixes DB :: clausedb2
  fixes frml_end :: nat
  fixes prf_next :: "'prf \<Rightarrow> int \<times> 'prf"
begin
  interpretation GRAT_def_loc DB frml_end prf_next .

  abbreviation "state_assn' \<equiv> cm_assn \<times>\<^sub>a assignment_assn"
  type_synonym i_state' = "i_cm \<times> i_assignment"  
      
  term parse_prf2 thm    parse_prf2_def
      
  lemmas [intf_of_assn] = 
    intf_of_assnI[where R="prfi_assn" and 'a="'prf i_prfi"]
    intf_of_assnI[where R="prfn_assn" and 'a="'prf i_prfn"]
    
  term mkp_raw_err  
  lemma mkp_raw_err_hnr[sepref_fr_rules]: 
    "(uncurry2 (return ooo mkp_raw_err), uncurry2 (RETURN ooo mkp_raw_err)) 
      \<in> id_assn\<^sup>k *\<^sub>a (option_assn int_assn)\<^sup>k *\<^sub>a (option_assn prfi_assn)\<^sup>k \<rightarrow>\<^sub>a errorp_assn"
    unfolding prfi_assn_def option_assn_pure_conv
    apply sepref_to_hoare
    by (sep_auto simp: prod_assn_def split: prod.split)
    
  sepref_register mkp_raw_err :: 
    "String.literal \<Rightarrow> int option \<Rightarrow> 'prf i_prfi option 
      \<Rightarrow> String.literal \<times> int option \<times> 'prf i_prfi option"
  
    
  definition "parse_prf_impl (prfn :: 'prf \<Rightarrow> int \<times> 'prf) \<equiv> \<lambda>(fuel::nat,prf). 
    if fuel > 0 then do {
      let (x,prf) = prfn prf;
      return (Inr (x,(fuel-1,prf)))
    } else 
      return (Inl (mkp_raw_err (STR ''Out of fuel'') None (Some (fuel, prf))))"
      
  lemma parse_prf_impl_hnr[sepref_fr_rules]:
    "(uncurry parse_prf_impl, uncurry parse_prf2) \<in> prfn_assn\<^sup>k *\<^sub>a prfi_assn\<^sup>d 
    \<rightarrow>\<^sub>a errorp_assn +\<^sub>a int_assn \<times>\<^sub>a prfi_assn"
    unfolding parse_prf_impl_def parse_prf2_def prfn_assn_def prfi_assn_def mkp_raw_err_def
    apply sepref_to_hoare 
    by sep_auto
  sepref_register parse_prf2 
    :: "'prf i_prfn \<Rightarrow> 'prf i_prfi \<Rightarrow> ('prf i_prfi error + int \<times> 'prf i_prfi) nres"    
      
    
  term read_clause_check_taut2    
      
  sepref_definition read_clause_check_taut3 is "uncurry3 read_clause_check_taut2"    
    :: "liti.a_assn\<^sup>k *\<^sub>a liti.it_assn\<^sup>k *\<^sub>a liti.it_assn\<^sup>k *\<^sub>a assignment_assn\<^sup>d 
      \<rightarrow>\<^sub>a errorp_assn +\<^sub>a liti.it_assn \<times>\<^sub>a bool_assn \<times>\<^sub>a assignment_assn"
    unfolding read_clause_check_taut2_def  
    supply [[goals_limit = 1]]  
    supply liti.itran_ord[dest]
    supply sum.splits[split]
    supply liti.itran_antisym[simp]  
    by sepref  
  lemmas [sepref_fr_rules] = read_clause_check_taut3.refine
  sepref_register read_clause_check_taut2 
    :: "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> i_assignment 
      \<Rightarrow> ('prf i_prfi error + nat \<times> bool \<times> i_assignment) nres"

  sepref_definition add_clause3 is "uncurry3 add_clause2" 
    :: "liti.a_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k *\<^sub>a liti.it_assn\<^sup>k *\<^sub>a cm_assn\<^sup>d \<rightarrow>\<^sub>a cm_assn"
    unfolding add_clause2_def 
    supply [[goals_limit = 1]]
    by sepref 
  sepref_register add_clause2 :: "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> i_cm \<Rightarrow> i_cm nres"
  lemmas [sepref_fr_rules] = add_clause3.refine  
    

  \<^cancel>\<open> TODO: Why can we rewrite 1::nat to int-itype? 
    Realized this oddity during debugging read_cnf_new2 sepref 
  \<close>
      
  sepref_definition read_cnf_new3 is "uncurry3 read_cnf_new2" 
    :: "liti.a_assn\<^sup>k *\<^sub>a liti.it_assn\<^sup>k *\<^sub>a liti.it_assn\<^sup>k *\<^sub>a cm_assn\<^sup>d 
      \<rightarrow>\<^sub>a errorp_assn +\<^sub>a cm_assn"   
    unfolding read_cnf_new2_def
    apply (rewrite at "(_,_,1,\<hole>)" assignment.fold_custom_empty)  
    supply [[id_debug, goals_limit=1]]  
    by sepref
  sepref_register read_cnf_new2 
    :: "int list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> i_cm \<Rightarrow> ('prf i_prfi error + i_cm) nres"      
  lemmas [sepref_fr_rules] = read_cnf_new3.refine  
    
  sepref_definition parse_check_blocked3 is "uncurry2 parse_check_blocked2"
    :: "liti.a_assn\<^sup>k *\<^sub>a assignment_assn\<^sup>d *\<^sub>a liti.it_assn\<^sup>k 
      \<rightarrow>\<^sub>a errorp_assn +\<^sub>a 
          liti.it_assn 
       \<times>\<^sub>a (assignment_assn \<times>\<^sub>a list_set_assn id_assn) 
       \<times>\<^sub>a liti.it_assn"
    unfolding parse_check_blocked2_def
    apply (rewrite at "(_, _, \<hole>)" ls.fold_custom_empty)
    apply (rewrite in "insert (var_of_lit _) _" fold_set_insert_dj)
    supply split[sepref_opt_simps]
    supply [[goals_limit = 1]]  
    by sepref
      
  term parse_check_blocked2    
  sepref_register parse_check_blocked2
    :: "int list \<Rightarrow> i_assignment \<Rightarrow> nat 
      \<Rightarrow> ('prf i_prfi error + nat \<times> (i_assignment \<times> nat set) \<times> nat) nres"
  lemmas [sepref_fr_rules] = parse_check_blocked3.refine
      
  sepref_definition check_unit_clause3 is "uncurry2 check_unit_clause2"
    :: "liti.a_assn\<^sup>k *\<^sub>a assignment_assn\<^sup>k *\<^sub>a (liti.it_assn)\<^sup>k 
        \<rightarrow>\<^sub>a sum_assn errorp_assn (pure lit_rel)"
    unfolding check_unit_clause2_def
    supply option.split_asm[split] \<^cancel>\<open> FIXME: Extra setup should not be necessary to translate if (x\<noteq>None) then ... the x \<close>
    by sepref
  lemmas [sepref_fr_rules] = check_unit_clause3.refine
  sepref_register check_unit_clause2 
    :: "int list \<Rightarrow> i_assignment \<Rightarrow> nat \<Rightarrow> ('prf i_prfi error + nat literal) nres"
  
  sepref_definition resolve_id3 is "uncurry resolve_id2" 
    :: "cm_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a sum_assn errorp_assn liti.it_assn"
    unfolding resolve_id2_def
    supply option.splits[split]
    by sepref
  term resolve_id2
  sepref_register "resolve_id2 
    :: (nat) clausemap1 \<Rightarrow> nat \<Rightarrow> _" :: "i_cm \<Rightarrow> nat \<Rightarrow> ('prf i_prfi error + nat) nres"
  lemmas [sepref_fr_rules] = resolve_id3.refine

  term   apply_units2
  sepref_definition apply_units3 is "uncurry4 apply_units2"
    :: "liti.a_assn\<^sup>k *\<^sub>a prfn_assn\<^sup>k *\<^sub>a cm_assn\<^sup>k *\<^sub>a (assignment_assn)\<^sup>d *\<^sub>a prfi_assn\<^sup>d 
      \<rightarrow>\<^sub>a errorp_assn +\<^sub>a assignment_assn \<times>\<^sub>a prfi_assn"
    unfolding apply_units2_def 
    by sepref 
  sepref_register "apply_units2 :: _ \<Rightarrow> _ \<Rightarrow> (nat) clausemap1 \<Rightarrow> _" 
      :: "int list \<Rightarrow> 'prf i_prfn \<Rightarrow> i_cm \<Rightarrow> i_assignment \<Rightarrow> 'prf i_prfi 
          \<Rightarrow> ('prf i_prfi error + i_assignment \<times> 'prf i_prfi) nres"
  lemmas [sepref_fr_rules] = apply_units3.refine
      
    
  \<^cancel>\<open> TODO: Use array-based list instead of list_set_assn! \<close>  
  sepref_definition apply_units3_bt is "uncurry5 apply_units2_bt"
    :: " liti.a_assn\<^sup>k 
      *\<^sub>a prfn_assn\<^sup>k
      *\<^sub>a cm_assn\<^sup>k 
      *\<^sub>a (assignment_assn)\<^sup>d 
      *\<^sub>a (list_set_assn nat_assn)\<^sup>d 
      *\<^sub>a prfi_assn\<^sup>d 
    \<rightarrow>\<^sub>a errorp_assn +\<^sub>a 
        (assignment_assn \<times>\<^sub>a list_set_assn nat_assn) \<times>\<^sub>a prfi_assn"
    unfolding apply_units2_bt_def 
    apply (rewrite in "insert (var_of_lit _) _" fold_set_insert_dj)
    supply [[id_debug, goals_limit = 1]]
    by sepref
      
  sepref_register "apply_units2_bt :: _ \<Rightarrow> _ \<Rightarrow> (nat) clausemap1 \<Rightarrow> _" 
      :: "int list \<Rightarrow> 'prf i_prfn \<Rightarrow> i_cm \<Rightarrow> i_assignment \<Rightarrow> nat set \<Rightarrow> 'prf i_prfi 
        \<Rightarrow> ('prf i_prfi error + (i_assignment \<times> nat set) \<times> 'prf i_prfi) nres"
  lemmas [sepref_fr_rules] = apply_units3_bt.refine
      
  term remove_ids2
  sepref_definition remove_ids3 is "uncurry2 remove_ids2"
    :: "prfn_assn\<^sup>k *\<^sub>a cm_assn\<^sup>d *\<^sub>a prfi_assn\<^sup>d 
        \<rightarrow>\<^sub>a errorp_assn +\<^sub>a cm_assn \<times>\<^sub>a prfi_assn"
    unfolding remove_ids2_def
    supply [[id_debug, goals_limit = 1]]
    by sepref
  sepref_register "remove_ids2 :: _ \<Rightarrow> (nat) clausemap1 \<Rightarrow> _"
    :: "'prf i_prfn \<Rightarrow> i_cm \<Rightarrow> 'prf i_prfi \<Rightarrow> ('prf i_prfi error + i_cm \<times> 'prf i_prfi) nres"
  lemmas [sepref_fr_rules] = remove_ids3.refine

    
  term check_conflict_clause2
  sepref_definition check_conflict_clause3 is "uncurry3 check_conflict_clause2"
    :: "liti.a_assn\<^sup>k *\<^sub>a prfi_assn\<^sup>k *\<^sub>a assignment_assn\<^sup>k *\<^sub>a liti.it_assn\<^sup>k 
        \<rightarrow>\<^sub>a sum_assn errorp_assn unit_assn"
    unfolding check_conflict_clause2_def
    supply [[id_debug, goals_limit = 1]]
    by sepref
  sepref_register check_conflict_clause2 
    :: "int list \<Rightarrow> 'prf i_prfi \<Rightarrow> i_assignment \<Rightarrow> nat \<Rightarrow> ('prf i_prfi error + unit) nres"
  lemmas [sepref_fr_rules] = check_conflict_clause3.refine

  term and_not_C_excl2  
  sepref_definition and_not_C_excl3 is "uncurry3 and_not_C_excl2"
    :: "liti.a_assn\<^sup>k *\<^sub>a (assignment_assn)\<^sup>d *\<^sub>a (liti.it_assn)\<^sup>k *\<^sub>a (pure lit_rel)\<^sup>k 
        \<rightarrow>\<^sub>a prod_assn assignment_assn (list_set_assn nat_assn)"
    unfolding and_not_C_excl2_def
    apply (rewrite at "(_,_,\<hole>)" ls.fold_custom_empty)
    apply (rewrite in "insert (var_of_lit _) _" fold_set_insert_dj)
    by sepref
  sepref_register and_not_C_excl2 
    :: "int list \<Rightarrow> i_assignment \<Rightarrow> nat \<Rightarrow> nat literal 
      \<Rightarrow> (i_assignment \<times> nat set) nres"    
  lemmas [sepref_fr_rules] = and_not_C_excl3.refine
      
      
  sepref_definition lit_in_clause_and_not_true3 
    is "uncurry3 lit_in_clause_and_not_true2"
    :: "liti.a_assn\<^sup>k *\<^sub>a (assignment_assn)\<^sup>k *\<^sub>a liti.it_assn\<^sup>k *\<^sub>a (pure lit_rel)\<^sup>k 
        \<rightarrow>\<^sub>a bool_assn"
    unfolding lit_in_clause_and_not_true2_def
    by sepref
  lemmas [sepref_fr_rules] = lit_in_clause_and_not_true3.refine  
  sepref_register "lit_in_clause_and_not_true2"
    :: "int list \<Rightarrow> (nat,bool) i_map \<Rightarrow> nat \<Rightarrow> nat literal \<Rightarrow> bool nres"
  
  sepref_definition get_rat_candidates3 is "uncurry3 get_rat_candidates2" 
    :: "liti.a_assn\<^sup>k *\<^sub>a cm_assn\<^sup>k *\<^sub>a (assignment_assn)\<^sup>k *\<^sub>a (pure lit_rel)\<^sup>k 
        \<rightarrow>\<^sub>a sum_assn errorp_assn (list_set_assn nat_assn)"
    unfolding get_rat_candidates2_def
    supply option.splits[split]
    apply (rewrite ndls.fold_custom_empty)
    apply (rewrite in "RETURN (Inr \<hole>)" fold_ndls_ls_copy)  
    by sepref  
      
  sepref_register get_rat_candidates2 
    :: "int list \<Rightarrow> i_cm \<Rightarrow> i_assignment \<Rightarrow> nat literal 
      \<Rightarrow> ('prf i_prfi error + nat set) nres"    
  lemmas [sepref_fr_rules] = get_rat_candidates3.refine  
      
  sepref_definition backtrack3 is "uncurry backtrack2"
    :: "(assignment_assn)\<^sup>d *\<^sub>a (list_set_assn nat_assn)\<^sup>k \<rightarrow>\<^sub>a assignment_assn"
    unfolding backtrack2_def
    by sepref  
  sepref_register "backtrack2 :: (nat\<rightharpoonup>bool) \<Rightarrow> _" 
    :: "i_assignment \<Rightarrow> nat set \<Rightarrow> i_assignment nres"
  lemmas [sepref_fr_rules] = backtrack3.refine  

    
  \<^cancel>\<open> TODO: Make this a proper operation on CM ?\<close>  
  lemma not_in_cm_ids_unf: "i\<notin>cm_ids CM \<longleftrightarrow> (case CM of (CM,_) \<Rightarrow> is_None (CM i))"  
    unfolding cm_ids_def by (cases CM) (auto split: option.splits)
    
  sepref_definition check_rup_proof3 is "uncurry4 check_rup_proof2"
    :: "liti.a_assn\<^sup>k *\<^sub>a prfn_assn\<^sup>k *\<^sub>a (state_assn')\<^sup>d *\<^sub>a liti.it_assn\<^sup>k *\<^sub>a prfi_assn\<^sup>d
        \<rightarrow>\<^sub>a errorp_assn +\<^sub>a state_assn' \<times>\<^sub>a liti.it_assn \<times>\<^sub>a prfi_assn"
    unfolding check_rup_proof2_def 
    apply (rewrite not_in_cm_ids_unf)
    by sepref  
  sepref_register check_rup_proof2 
    :: "int list \<Rightarrow> 'prf i_prfn \<Rightarrow> i_state' \<Rightarrow> nat \<Rightarrow> 'prf i_prfi 
      \<Rightarrow> ('prf i_prfi error + i_state' \<times> nat \<times> 'prf i_prfi) nres"
  lemmas [sepref_fr_rules] = check_rup_proof3.refine  

  term lit_in_clause2
  sepref_definition lit_in_clause3 is "uncurry2 lit_in_clause2" 
    :: "liti.a_assn\<^sup>k *\<^sub>a liti.it_assn\<^sup>k *\<^sub>a lit_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
    unfolding lit_in_clause2_def
    by sepref  
  sepref_register lit_in_clause2 :: "int list \<Rightarrow> nat \<Rightarrow> nat literal \<Rightarrow> bool nres"        
  lemmas [sepref_fr_rules] = lit_in_clause3.refine  
    
  term check_rat_candidates_part2  
  sepref_definition check_rat_candidates_part3 
    is "uncurry6 check_rat_candidates_part2" ::
    "    liti.a_assn\<^sup>k 
      *\<^sub>a prfn_assn\<^sup>k
      *\<^sub>a cm_assn\<^sup>k 
      *\<^sub>a lit_assn\<^sup>k 
      *\<^sub>a (list_set_assn nat_assn)\<^sup>d 
      *\<^sub>a assignment_assn\<^sup>d 
      *\<^sub>a prfi_assn\<^sup>d 
    \<rightarrow>\<^sub>a errorp_assn +\<^sub>a (assignment_assn \<times>\<^sub>a prfi_assn)"
    unfolding check_rat_candidates_part2_def
    supply [[goals_limit = 1, id_debug]]  
    by sepref \<^cancel>\<open> Takes looong \<close>  
  sepref_register "check_rat_candidates_part2 :: _ \<Rightarrow> _ \<Rightarrow> (nat) clausemap1 \<Rightarrow> _" 
    :: "int list \<Rightarrow> 'prf i_prfn \<Rightarrow> i_cm \<Rightarrow> nat literal \<Rightarrow> nat set \<Rightarrow> i_assignment \<Rightarrow> 'prf i_prfi 
        \<Rightarrow> ('prf i_prfi error + i_assignment \<times> 'prf i_prfi) nres"
  lemmas [sepref_fr_rules] = check_rat_candidates_part3.refine  
      
  term check_rat_proof2    
  sepref_definition check_rat_proof3 is "uncurry4 check_rat_proof2"
    :: "liti.a_assn\<^sup>k *\<^sub>a prfn_assn\<^sup>k *\<^sub>a (state_assn')\<^sup>d *\<^sub>a liti.it_assn\<^sup>k *\<^sub>a prfi_assn\<^sup>d
      \<rightarrow>\<^sub>a errorp_assn +\<^sub>a state_assn' \<times>\<^sub>a liti.it_assn \<times>\<^sub>a prfi_assn"
    unfolding check_rat_proof2_def short_circuit_conv
    supply [[goals_limit = 1, id_debug]]  
    supply if_splits[split!]
    apply (rewrite not_in_cm_ids_unf)    
    by sepref \<^cancel>\<open> Takes looong \<close> 
  sepref_register check_rat_proof2 
    :: "int list \<Rightarrow> 'prf i_prfn \<Rightarrow> i_state' \<Rightarrow> nat \<Rightarrow> 'prf i_prfi 
      \<Rightarrow> ('prf i_prfi error + i_state' \<times> nat \<times> 'prf i_prfi) nres"
  lemmas [sepref_fr_rules] = check_rat_proof3.refine  

  term check_item2    
  sepref_definition check_item3 is "uncurry4 check_item2"  
    :: "liti.a_assn\<^sup>k *\<^sub>a prfn_assn\<^sup>k *\<^sub>a (state_assn')\<^sup>d *\<^sub>a liti.it_assn\<^sup>k *\<^sub>a prfi_assn\<^sup>d
        \<rightarrow>\<^sub>a errorp_assn +\<^sub>a option_assn (state_assn' \<times>\<^sub>a liti.it_assn \<times>\<^sub>a prfi_assn)"
    unfolding check_item2_def 
    supply [[goals_limit = 1, id_debug]]  
    by sepref  
  sepref_register check_item2 
    :: "int list \<Rightarrow> 'prf i_prfn \<Rightarrow> i_state' \<Rightarrow> nat \<Rightarrow> 'prf i_prfi 
      \<Rightarrow> ('prf i_prfi error + (i_state' \<times> nat \<times> 'prf i_prfi) option) nres"    
  lemmas [sepref_fr_rules] = check_item3.refine  
    
  term is_syn_taut2    
  sepref_definition is_syn_taut3 is "uncurry2 is_syn_taut2"
    :: "liti.a_assn\<^sup>k *\<^sub>a liti.it_assn\<^sup>k *\<^sub>a assignment_assn\<^sup>d 
        \<rightarrow>\<^sub>a bool_assn \<times>\<^sub>a assignment_assn"
    unfolding is_syn_taut2_def
    by sepref 
  sepref_register is_syn_taut2 
    :: "int list \<Rightarrow> nat \<Rightarrow> i_assignment \<Rightarrow> (bool \<times> i_assignment) nres"    
  lemmas [sepref_fr_rules] = is_syn_taut3.refine  
      
  \<^cancel>\<open>  
  term read_cnf2    
  sepref_definition read_cnf3 is "uncurry2 read_cnf2" 
    :: "liti.a_assn\<^sup>k *\<^sub>a (list_assn liti.it_assn)\<^sup>k *\<^sub>a cm_assn\<^sup>d 
        \<rightarrow>\<^sub>a cm_assn \<times>\<^sub>a nat_assn"
    unfolding read_cnf2_def 
    supply [[goals_limit = 1, id_debug]]  
    apply (rewrite at "(_,1,\<hole>)" assignment.fold_custom_empty)  
    by sepref  
  sepref_register read_cnf2 
    :: "int list \<Rightarrow> nat list \<Rightarrow> i_cm \<Rightarrow> (i_cm \<times> nat) nres" 
  lemmas [sepref_fr_rules] = read_cnf3.refine  
  \<close>

  \<^cancel>\<open>term goto_next_item2
  thm goto_next_item2_def
  \<^cancel>\<open> TODO: frml_end parameter only gets in by assertion! Remove assertion before!
      Currently solved by inlining goto_next_item2
  \<close>\<close>

  term   init_rat_counts2
  sepref_definition init_rat_counts3 is "uncurry init_rat_counts2" 
    :: "prfn_assn\<^sup>k *\<^sub>a prfi_assn\<^sup>d \<rightarrow>\<^sub>a errorp_assn +\<^sub>a (cm_assn \<times>\<^sub>a prfi_assn)"
    unfolding init_rat_counts2_def cm_empty1_def
    apply (rewrite at "(\<hole>,_)" amd.fold_custom_empty)
    apply (rewrite at "(_,\<hole>)" creg.fold_custom_empty) 
    apply (rewrite at "RETURN (_,\<hole>)" op_creg_initialize_def[symmetric])  
    supply [[goals_limit = 1, id_debug]]  
    by sepref 
  sepref_register init_rat_counts2 
    :: "'prf i_prfn \<Rightarrow> 'prf i_prfi \<Rightarrow> ('prf i_prfi error + i_cm \<times> 'prf i_prfi) nres"
  lemmas [sepref_fr_rules] = init_rat_counts3.refine  
    
  term verify_unsat2    
  sepref_definition verify_unsat3 is "uncurry5 verify_unsat2" 
    :: "   liti.a_assn\<^sup>k 
        *\<^sub>a prfn_assn\<^sup>k
        *\<^sub>a liti.it_assn\<^sup>k 
        *\<^sub>a liti.it_assn\<^sup>k 
        *\<^sub>a liti.it_assn\<^sup>k 
        *\<^sub>a prfi_assn\<^sup>d 
      \<rightarrow>\<^sub>a errorp_assn +\<^sub>a unit_assn"  
    unfolding verify_unsat2_def 
    apply (rewrite at "Let (_,\<hole>)" assignment.fold_custom_empty)  
    \<^cancel>\<open>apply (rewrite at "do {let it\<^sub>0 = \<hole>;
                             _ \<leftarrow> ASSERT (_ \<noteq> None);
                             let s = the _; _}" fold_COPY)  \<close>
    supply [[goals_limit = 1, id_debug]]  
    supply option.splits[split] \<^cancel>\<open> TODO: The should be translated without extra setup \<close>  
    by sepref

end      


definition "verify_unsat_split_impl_wrapper DBi prf_next F_end it prf \<equiv> do {
  lenDBi \<leftarrow> Array.len DBi;

  if (0 < F_end \<and> F_end \<le> lenDBi \<and> 0 < it \<and> it \<le> lenDBi) then
    verify_unsat3 DBi prf_next 1 F_end it prf
  else
    return (Inl (STR ''Invalid arguments'',None,None))
}"
  
lemmas [code] = DB2_def_loc.item_next_impl_def
export_code verify_unsat_split_impl_wrapper checking SML_imp  
  
  
subsection \<open>Correctness Theorem\<close>  
  
context GRAT_loc begin  
  
  lemma verify_unsat3_correct_aux[sep_heap_rules]:
    \<^cancel>\<open>assumes F_ref: "(Fi,F) \<in> \<langle>cref_rel\<rangle>list_rel"\<close>
    assumes SEG: "liti.seg F_begin lst F_end"
    assumes itI[simp]: "it_invar F_end" "it_invar it"
    shows "
      <DBi \<mapsto>\<^sub>a DB> 
        verify_unsat3 DBi prf_next F_begin F_end it prf
      <\<lambda>r. DBi \<mapsto>\<^sub>a DB * \<up>(\<not>isl r \<longrightarrow> F_invar lst \<and> \<not>sat (F_\<alpha> lst))>\<^sub>t"
  proof -
    note verify_unsat2.refine[OF GRAT_loc_axioms, symmetric, THEN meta_eq_to_obj_eq] 
    also note verify_unsat2_loc.refine[symmetric,THEN meta_eq_to_obj_eq] 
    also note verify_unsat1_bd.refine[symmetric]  
    also note verify_unsat1_refine[OF IdI IdI IdI]
    also note verify_unsat_bt_refine[OF IdI IdI IdI]
    also note verify_unsat_correct[OF SEG itI]
    finally have C1: "verify_unsat2 DB prf_next F_begin F_end it prf
        \<le> ESPEC (\<lambda>_. True) (\<lambda>_.  F_invar lst \<and> \<not> sat ((F_\<alpha> lst)))" 
      by (auto simp: pw_ele_iff refine_pw_simps)
        
    from C1 have NF: "nofail (verify_unsat2 DB prf_next F_begin F_end it prf)" 
      by (auto simp: pw_ele_iff refine_pw_simps)
        
    note A = verify_unsat3.refine[of DB, to_hnr]
    note A = A[
        of "prf" "prf" it it F_end F_end F_begin F_begin prf_next prf_next DB DBi,
        unfolded autoref_tag_defs]  
    note A = A[THEN hn_refineD]
    note A = A[OF NF]
    note A = A[ 
        unfolded hn_ctxt_def liti.it_assn_def liti.a_assn_def
          b_assn_pure_conv list_assn_pure_conv sum_assn_pure_conv 
          option_assn_pure_conv prod_assn_pure_conv,
        unfolded pure_def,
        simplified, rule_format
        ]
    
    from C1 have 1: "RETURN x \<le> verify_unsat2 DB prf_next F_begin F_end it prf
      \<Longrightarrow> \<not>isl x \<longrightarrow> F_invar lst \<and> \<not>sat (F_\<alpha> lst)" for x
      unfolding enres_unfolds
      apply (cases x)  
      apply (auto simp: pw_le_iff refine_pw_simps)  
      done  
      
    from SEG have I_begin: "liti.I F_begin" by auto
        
    show ?thesis  
      apply (rule cons_rule[OF _ _ A])
      applyS (sep_auto simp: prfi_assn_def prfn_assn_def pure_def)
      applyS (sep_auto dest!: 1 simp: sum.disc_eq_case split: sum.splits)
      applyS (simp add: I_begin)  
      done
  qed      
end    
   

text \<open>Main correctness theorem:
  Given an array @{term DBi} that contains the integers @{term DB}, 
  the verification algorithm does not change the array, and if it returns a 
  non-@{const Inl} value, the formula in the array is unsatisfiable.
\<close>  
theorem verify_unsat_split_impl_wrapper_correct[sep_heap_rules]: 
  shows "
    <DBi \<mapsto>\<^sub>a DB> 
      verify_unsat_split_impl_wrapper DBi prf_next F_end it prf
    <\<lambda>result. DBi \<mapsto>\<^sub>a DB * \<up>(\<not>isl result \<longrightarrow> verify_unsat_spec DB F_end)>\<^sub>t"
proof -
  {
    assume A: "1 \<le> F_end" "F_end \<le> length DB" "0 < it" "it \<le> length DB"
    
    then interpret GRAT_loc DB F_end 
      apply unfold_locales by auto
      
    have SEG: "liti.seg 1 (slice 1 F_end DB) F_end"
      using \<open>1 \<le> F_end\<close> \<open>F_end \<le> length DB\<close>
      by (simp add: liti.seg_sliceI)
     
    have INV: "it_invar F_end" "it_invar it" 
      subgoal 
        by (meson SEG it_end_invar it_invar_imp_ran 
            itran_invarD liti.itran_alt liti.itran_refl liti.seg_invar2)
      subgoal
        by (metis \<open>0 < it\<close> \<open>it \<le> length DB\<close> liti.seg_exists exists_leI 
            it_invar_imp_ran 
            itran_invarD it_end_invar liti.itran_alt liti.itran_refl 
            liti.seg_invar1) 
      done    
      
    have U1: "slice 1 F_end DB = tl (take F_end DB)"
      unfolding Misc.slice_def
      by (metis One_nat_def drop_0 drop_Suc_Cons drop_take list.sel(3) tl_drop)
        
    have U2: "F_invar (tl (take F_end DB)) \<and> \<not> sat (F_\<alpha> (tl (take F_end DB))) 
      \<longleftrightarrow> verify_unsat_spec DB F_end"    
      unfolding verify_unsat_spec_def clause_DB_valid_def clause_DB_sat_def 
      using A by auto

    note verify_unsat3_correct_aux[OF SEG INV, unfolded U1 U2]
  } note [sep_heap_rules] = this
  
  
  show ?thesis
    unfolding verify_unsat_split_impl_wrapper_def by sep_auto
qed      

end  
  
