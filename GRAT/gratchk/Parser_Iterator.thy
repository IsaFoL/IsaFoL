section \<open>Iterators and Simple Parsers\<close>
theory Parser_Iterator
imports "Array_Map_Default" Exc_Nres_Monad Dimacs_Format
begin
  text \<open>
    This theory provides a notion of iterator, and 
    defines simple parsers (for null-terminated lists) on top of this.
  \<close>

(* TODO: FIXME *)
hide_const Word.slice   

  
  subsection \<open>Iterators\<close>
  text \<open>This locale provides the abstract interface of an iterator.

    Note that there is no direct notion of reaching the end. 
    This is only indirectly modeled by the invariant not holding 
    for the iterator any more. Thus, algorithms against this 
    interface can only be written if one can derive from the precondition
    that the iterator will remain valid. 

    Two examples how this could be asserted are:
      \<^item> The precondition states that there is a string at the iterator position
      \<^item> There is an explicit iterator range \<open>begin \<dots> end\<close>, which is valid, 
        the current iterator is in between, and the algorithm stops
        if it reaches \<open>end\<close>.
  \<close>
  locale iterator = 
    fixes 
        I :: "'it::order \<Rightarrow> bool" \<comment> \<open>Iterator invariant\<close>
    and "next" :: "'it \<Rightarrow> 'it"   \<comment> \<open>Advance iterator\<close>  
    and peek :: "'it \<Rightarrow> 'a"      \<comment> \<open>Get element at current position\<close>
    assumes ordered: "I it \<Longrightarrow> it < next it"
      \<comment> \<open>Advancing an iterator must result in a bigger iterator.\<close>
  begin  
    subsubsection \<open>Segments\<close>
    primrec seg :: "'it \<Rightarrow> 'a list \<Rightarrow> 'it \<Rightarrow> bool" where
      "seg it [] it' \<longleftrightarrow> I it \<and> it'=it"
    | "seg it (x#xs) it' \<longleftrightarrow> I it \<and> x = peek it \<and> seg (next it) xs it'"  
      
    definition "itran it it' \<equiv> \<exists>l. seg it l it'"  
      
    lemma seg_invar1[simp]: "seg it xs it' \<Longrightarrow> I it" by (cases xs) auto
    lemma seg_invar2[simp]: "seg it xs it' \<Longrightarrow> I it'" 
      by (induction xs arbitrary: it) auto

    lemma itran_invar[simp]: assumes "itran it it'" shows "I it" "I it'"
      using assms
      unfolding itran_def
      by auto  

    lemma seg_I_next[simp, elim]: "\<lbrakk>seg it l it'; it\<noteq>it'\<rbrakk> \<Longrightarrow> I (next it)"
      by (cases l) auto

    lemma itran_I_next[simp, elim]: "\<lbrakk>itran it it'; it\<noteq>it'\<rbrakk> \<Longrightarrow> I (next it)"
      unfolding itran_def by auto
        
    lemma seg_concat[simp]: "seg it (xs@ys) it' 
      \<longleftrightarrow> (\<exists>ith. seg it xs ith \<and> seg ith ys it')"
      by (induction xs arbitrary: it) auto
      
    lemma seg_ord: "seg it l it' \<Longrightarrow> it \<le> it'"
      apply (induction l arbitrary: it) 
      using less_imp_le less_le_trans ordered by (auto; blast)+
  
    lemma itran_ord: "itran it it' \<Longrightarrow> it \<le> it'"
      by (auto simp: itran_def seg_ord)
        
    lemma seg_no_cyc[simp]: "\<not>seg (next it) list it"
      by (meson less_le_not_le ordered seg_invar2 seg_ord)
        
    lemma seg_eq_iff_empty[simp]: "seg it l it \<longleftrightarrow> I it \<and> l=[]"
      by (cases l) (auto)
        
    lemma seg_unique: "\<lbrakk> seg it l1 it'; seg it l2 it' \<rbrakk> \<Longrightarrow> l1=l2"    
    proof (induction l1 arbitrary: it l2)
      case Nil
      then show ?case by auto
    next
      case (Cons a l1)
      then show ?case by (cases l2) auto
    qed

    definition "the_seg it it' \<equiv> THE l. seg it l it'"
      
    lemma seg_the_seg: "itran it it' \<Longrightarrow> seg it (the_seg it it') it'"  
      unfolding itran_def the_seg_def
      by (metis seg_unique the_equality)  
      
    lemma the_seg_eq[simp]: "seg it l it' \<Longrightarrow> the_seg it it' = l"    
      unfolding itran_def the_seg_def
      by (metis seg_unique the_equality)  

    lemma the_seg_next_append: 
      assumes "seg it l it'" "itran it' (next it')"
      shows "the_seg it (next it') = l @ [peek it']"    
      apply (rule the_seg_eq)  
      using assms by auto  
        
    lemma itranE: assumes "itran it it'" obtains l where "seg it l it'"
      using assms unfolding itran_def by auto
      
    lemma itran_next[simp]: 
      "\<lbrakk>I it; it\<noteq>itE\<rbrakk> \<Longrightarrow> itran (next it) itE \<longleftrightarrow> itran it itE"  
      apply (rule iffI; clarsimp simp: itran_def)
      subgoal for l by (rule exI[where x="peek it#l"]) auto
      subgoal for l by (cases l) auto
      done    
          
    lemma itran_measure[simp]: 
      "\<lbrakk>itran it it'; it\<noteq>it'\<rbrakk> 
      \<Longrightarrow> length (the_seg (next it) it') < length (the_seg it it')"
      apply (erule itranE; simp)
      subgoal for l by (cases l) auto  
      done

    lemma itran_measure': 
      "\<lbrakk>itran it ith; itran ith it'; it\<noteq>ith \<rbrakk> 
      \<Longrightarrow> length (the_seg ith it') < length (the_seg it it')"
    proof (elim itranE; simp)
      fix l1 l2 
      assume "it \<noteq> ith" "seg it l1 ith" "seg ith l2 it'"
      hence [simp]: "l1\<noteq>[]" and S12: "seg it (l1@l2) it'" by auto
      show "length l2 < length (the_seg it it')" 
        using the_seg_eq[OF S12] by auto
    qed      

    lemma itran_refl[simp]: "itran it it \<longleftrightarrow> I it" by (auto simp: itran_def)
    lemma itran_antisym: "\<lbrakk>itran it it'; itran it' it\<rbrakk> \<Longrightarrow> it=it'" 
      by (auto dest!: itran_ord)
    lemma itran_trans[trans]: "itran it ith \<Longrightarrow> itran ith it' \<Longrightarrow> itran it it'"
      by (meson itran_def seg_concat)

    lemma itran_next2I: "\<lbrakk>itran it it'; I (next it')\<rbrakk> \<Longrightarrow> itran it (next it')"
      by (metis itran_invar(2) itran_next itran_refl itran_trans)
        
    subsubsection \<open>Zero-Terminated Strings\<close>
    definition "lz_string Z it l it' \<equiv> seg it (l@[Z]) it' \<and> Z\<notin>set l"

    lemma lz_string_empty[simp]: 
      "lz_string Z ith [] it' 
      \<longleftrightarrow> I ith \<and> I (next ith) \<and> peek ith=Z \<and> it'=next ith"  
      unfolding lz_string_def
      by auto  
      
    lemma lz_string_cons[simp]: "lz_string Z it (x#xs) it' 
      \<longleftrightarrow> I it \<and> x=peek it \<and> x\<noteq>Z \<and> lz_string Z (next it) xs it'"    
      unfolding lz_string_def
      by auto  
        
    lemma lz_string_invar[simp]: 
      assumes "lz_string Z it l it'" shows "I it" "I it'"
      using assms unfolding lz_string_def by auto
        
    lemma lz_string_noZ: "lz_string Z it l it' \<Longrightarrow> Z\<notin>set l" 
      unfolding lz_string_def by auto
        
    lemma lz_string_determ: 
      assumes "lz_string Z it l it'"
      assumes "lz_string Z it l' it''"
      shows "l'=l \<and> it''=it'"  
      using assms 
    proof (induction l arbitrary: l' it)
      case Nil thus ?case by (cases l'; auto)
    next
      case (Cons a l) thus ?case by (cases l'; auto)
    qed
        
    definition "the_lz_string Z it \<equiv> THE l. \<exists>it'. lz_string Z it l it'"
      
    lemma the_lz_string_eq[simp]: 
      "lz_string Z it l it' \<Longrightarrow> the_lz_string Z it = l"  
      unfolding the_lz_string_def
      using lz_string_determ by blast  
      
    definition "parse_lz ERR Z itE it c f s \<equiv> doE {
      CHECK (it\<noteq>itE) ERR;
      (it,s) \<leftarrow> EWHILEIT 
        (\<lambda>(it,s). I it \<and> itran it itE \<and> it\<noteq>itE) 
        (\<lambda>(it,s). peek it \<noteq> Z \<and> c s) 
        (\<lambda>(it,s). doE {
          EASSERT (itran it itE \<and> it \<noteq> itE);
          let x = peek it;
          EASSERT (x \<noteq> Z);
          s \<leftarrow> f x s;
          let it = next it; 
          CHECK (it\<noteq>itE) ERR;
          ERETURN (it,s)
        }) (it,s);
      EASSERT (itran it itE \<and> it \<noteq> itE);
      let it = next it;
      ERETURN (it,s)
    }"  
        
    lemma parse_lz_rule:
      assumes \<Phi>: "\<Phi> [] s"
      assumes IT: "itran it itE"
      assumes C_RL: "\<And>x l s. \<lbrakk>\<Phi> l s; x\<noteq>Z; c s\<rbrakk> \<Longrightarrow> f x s \<le> ESPEC E (\<Phi> (l@[x]))"
      assumes IMP_Q: "\<And>it' s l. 
        \<lbrakk>lz_string Z it l it'; itran it' itE; \<Phi> l s; I it'; c s\<rbrakk> \<Longrightarrow> Q (it',s)"
      assumes IMP_INTR: "\<And>it' s l. 
        \<lbrakk> itran it it'; itran it' itE; Z\<notin>set l; \<Phi> l s; \<not>c s \<rbrakk> \<Longrightarrow> Q (it',s)"  
      assumes IMP_E: "Z \<notin> set (the_seg it itE) \<Longrightarrow> E ERR"  
      shows "parse_lz ERR Z itE it c f s \<le> ESPEC E Q"
      unfolding parse_lz_def  
      apply (refine_vcg 
          EWHILEIT_expinv_rule[where 
                I="\<lambda>(it',s). \<exists>l. seg it l it' 
                              \<and> itran it' itE \<and> it'\<noteq>itE \<and> Z\<notin>set l \<and> \<Phi> l s"
            and R="measure (\<lambda>(it',_). length (the_seg it' itE))"
          ])  
      apply (vc_solve simp: \<Phi> IT itran_invar[OF IT])
      subgoal for it' s l  
        apply (refine_vcg C_RL[of l, THEN ESPEC_trans])
        apply (vc_solve simp: the_seg_next_append)
        subgoal for s' apply (rule exI[where x="l@[peek it']"]) by auto
        subgoal apply (rule IMP_E) by (auto simp: the_seg_next_append)
        done
      subgoal for it' s l 
      proof -
        assume a1: "\<Phi> l s"
        assume a2: "it' \<noteq> itE"
        assume a3: "Z \<notin> set l"
        assume a4: "itran it' itE"
        assume a5: "seg it l it'"
        assume a6: "peek it' = Z \<or> \<not> c s"
        have f7: "\<not> I it' \<or> itran (next it') itE"
          using a4 a2 itran_next by blast
        have f8: "\<And>i. \<not> I (next i) \<or> \<not> I i \<or> next i = i \<or> itran i (next i)"
          by (metis (no_types) itran_next itran_refl)
        then have "the_seg it (next it') = l @ [peek it']"
          using a5 a4 a2 
          by (metis (full_types) itran_I_next itran_def itran_invar(2) 
                    itran_refl the_seg_next_append)
        then show ?thesis
          using f8 f7 a6 a5 a4 a3 a2 a1 
          by (metis IMP_INTR IMP_Q itran_I_next itran_def itran_invar(2) 
                    itran_trans lz_string_def seg_the_seg)
      qed
      subgoal apply (rule IMP_E) using IT by auto
      done    
        

    definition "iterate_lz Z itE it c f s \<equiv> doE {
      EASSERT (it\<noteq>itE);
      (it,s) \<leftarrow> EWHILEIT 
        (\<lambda>(it,s). I it \<and> itran it itE \<and> it\<noteq>itE) 
        (\<lambda>(it,s). peek it \<noteq> Z \<and> c s) 
        (\<lambda>(it,s). doE {
          EASSERT (itran it itE \<and> it \<noteq> itE);
          let x = peek it;
          EASSERT (x \<noteq> Z);
          s \<leftarrow> f x s;
          let it = next it; 
          ERETURN (it,s)
        }) (it,s);
      ERETURN s
    }"  

    lemma iterate_lz_rule:
      assumes P: "lz_string Z it l it'" "itran it' itE"
      assumes \<Phi>: "\<Phi> [] l s"
      assumes F_RL: "\<And>x l1 l2 s. \<lbrakk> l = l1@x#l2; \<Phi> l1 (x#l2) s; c s\<rbrakk> 
                      \<Longrightarrow> f x s \<le> ESPEC \<Psi> (\<Phi> (l1@[x]) l2)"
      assumes IMP_INTR: "\<And>l1 l2 s. \<lbrakk> l = l1@l2; \<Phi> l1 l2 s; \<not>c s \<rbrakk> \<Longrightarrow> Q s"  
      assumes IMP_Q: "\<And>s. \<lbrakk> \<Phi> l [] s; c s \<rbrakk> \<Longrightarrow> Q s"
      shows "iterate_lz Z itE it c f s \<le> ESPEC \<Psi> Q"
    proof -  
      from P have 1: "I it" and [simp]: "it\<noteq>itE"
        apply -
        subgoal by auto  
        subgoal
          by (metis Nil_is_append_conv itran_antisym itran_def list.simps(3) 
                    lz_string_def seg_eq_iff_empty)   
        done
      
      show ?thesis
        unfolding iterate_lz_def
        apply (refine_vcg EWHILEIT_expinv_rule[where 
                  I = "\<lambda>(ith,s). \<exists>l1 l2. seg it l1 ith 
                        \<and> lz_string Z ith l2 it' \<and> l=l1@l2 \<and> \<Phi> l1 l2 s"
              and R = "measure (\<lambda>(ith,_). length (the_seg ith it'))"    
              ])  
        apply (vc_solve simp: P \<Phi> 1)
        subgoal using P(2) itran_def itran_trans lz_string_def by blast  
        subgoal
          by (metis Nil_is_append_conv assms(2) itran_antisym itran_def 
                    lz_string_def lz_string_empty seg_eq_iff_empty)  
        subgoal for ith s l1 l2
          apply (cases l2; simp)
          subgoal for l2'  
            apply (refine_vcg F_RL[of l1 _ "tl l2",THEN ESPEC_trans])
            apply vc_solve
            subgoal by (rule exI[where x="l1@[peek ith]"]) auto
            subgoal by (metis itran_def itran_measure itran_next lz_string_def 
                              seg_invar2 seg_no_cyc)
            done
          done
        subgoal by (metis IMP_INTR IMP_Q append_Nil2 
                          list.exhaust lz_string_cons)
        subgoal using assms(2) itran_def itran_trans lz_string_def by blast    
        subgoal
          by (metis Nil_is_append_conv assms(2) itran_antisym itran_def
              lz_string_def lz_string_empty seg_eq_iff_empty seg_no_cyc)    
        done
    qed
      
    lemmas [enres_inline] = parse_lz_def iterate_lz_def     
  end  
    
  subsection \<open>Tokenization\<close>  
  (*
  text \<open>We first define a function that joins a list of lists, 
    terminating each sublist by a zero.\<close>
  primrec concat_sep :: "'a \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
    "concat_sep Z [] = []"
  | "concat_sep Z (l#ls) = l @ Z # concat_sep Z ls"  
    
  lemma concat_sep_empty_iff[simp]: "concat_sep Z ls = [] \<longleftrightarrow> ls=[]"  
    by (cases ls) auto
    
  lemma concat_sep_by_concat_map: 
    "concat_sep x ll = concat (map (\<lambda>l . l@[x]) ll)"
    by (induction ll) auto  
      
      
      
  text \<open>Then, we first define the tokenization function operationally. 
    Later, we will characterize it as the unique inverse of concatenation.\<close>  
  fun tokenize :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
    "tokenize Z [] = []"
  | "tokenize Z ([x]) = (if x=Z then [[]] else undefined)"  
  | "tokenize Z (x#xs) = (
        if x=Z then []#tokenize Z xs 
        else case tokenize Z xs of l#ls \<Rightarrow> (x#l)#ls | _ \<Rightarrow> undefined
    )"  
    
  lemma tokenize_ZZ[simp]: 
    "tokenize Z (Z#l) = (if l=[] then [[]] else []#tokenize Z l)"  
    by (auto simp: neq_Nil_conv)
      
  lemma tokenize_NZZ: "\<lbrakk>Z \<notin> set l\<rbrakk> \<Longrightarrow> 
    tokenize Z (l @ Z # l') = (if l' = [] then [l] else l#tokenize Z l')"
    by (induction l rule: tokenize.induct) auto  
    
  lemma tokenize_NZZE[simp]: "Z \<notin> set l \<Longrightarrow> tokenize Z (l @ [Z]) = [l]"    
    by (simp add: tokenize_NZZ)
      
  lemma concat_tokenize_id: 
    "\<lbrakk> l\<noteq>[] \<longrightarrow> last l = Z \<rbrakk> \<Longrightarrow> concat_sep Z (tokenize Z l) = l"  
    apply (induction l rule: tokenize.induct)
    apply (auto split: list.split)
    done  
    
  lemma tok_eq_prefixD: "\<lbrakk>l@Z#m = l'@Z#m'; Z\<notin>set l; Z\<notin>set l'\<rbrakk> \<Longrightarrow> l'=l \<and> m'=m"    
    by (metis in_set_conv_decomp list_match_lel_lel)
      
  lemma concat_sep_unique:
    assumes "Z \<notin> \<Union>set (map set ls1)" 
    assumes "Z \<notin> \<Union>set (map set ls2)" 
    assumes "concat_sep Z ls1 = concat_sep Z ls2"
    shows "ls1 = ls2"    
    using assms
    apply (induction ls1 arbitrary: ls2)
    subgoal for ls2 by (cases ls2) auto  
    subgoal for l ls1 ls2 by (cases ls2) (auto dest: tok_eq_prefixD)
    done    
        
  lemma tokenize_not_empty[simp]: "\<lbrakk>l\<noteq>[]; last l = Z\<rbrakk> \<Longrightarrow> tokenize Z l \<noteq> []"    
    by (induction l rule: tokenize.induct) (auto split: list.splits)
      
  lemma tokenize_complete: 
    "\<lbrakk>l\<noteq>[] \<longrightarrow> last l = Z\<rbrakk> \<Longrightarrow> Z \<notin> \<Union>set (map set (tokenize Z l))"
    by (induction l rule: tokenize.induct) (auto split: list.splits)

  lemma tokenize_complete_set: 
    "\<lbrakk> ll\<noteq>[] \<longrightarrow> last ll = Z; l \<in> set (tokenize Z ll); x\<in>set l \<rbrakk> \<Longrightarrow> x\<noteq>Z"  
    by (drule tokenize_complete) auto  
      
      
  lemma unique_tokenization: 
    "\<lbrakk> l\<noteq>[] \<longrightarrow> last l = Z \<rbrakk> 
    \<Longrightarrow> \<exists>!ls. (Z\<notin>\<Union>set (map set ls) \<and> concat_sep Z ls = l)"
    apply (frule concat_tokenize_id)
    apply (frule tokenize_complete)
    apply (rule ex1I[where a="tokenize Z l"])
    subgoal by auto
    subgoal using concat_sep_unique by fastforce  
    done    
    
  lemma tokenize_append: 
    "\<lbrakk> l\<noteq>[] \<longrightarrow> last l=Z \<rbrakk> \<Longrightarrow> tokenize Z (l@l') = tokenize Z l @ tokenize Z l'"    
    by (induction Z\<equiv>Z l rule: tokenize.induct) (auto split: list.split)
      
      
  lemma concat_sep_last_sep: "\<lbrakk>concat_sep Z ll = l; l \<noteq> []\<rbrakk> \<Longrightarrow> last l = Z"  
    by (induction ll arbitrary: l) (auto split: if_splits)
      
      
      
  text \<open>
    We specify the result of tokenize to be the unique list of lists, which, when joined,
    yields the original list again. To believe this characterization, you have to believe that
    @{const \<open>concat_sep\<close>} does the right thing 
    (e.g.\ look at @{thm [source] concat_sep_by_concat_map}), and have a look 
    at @{thm [source] unique_tokenization}
    to persuade yourself that the right-hand side is well-defined.
  \<close>
  theorem tokenize_spec: "\<lbrakk> l\<noteq>[] \<longrightarrow> last l = Z \<rbrakk> 
    \<Longrightarrow> tokenize Z l = (THE ls. Z\<notin>\<Union>set (map set ls) \<and> concat_sep Z ls = l)"
    apply (frule theI'[OF unique_tokenization])
    by (metis (no_types, lifting) concat_sep_unique concat_tokenize_id 
              tokenize_complete)
      
      
  lemma tokenize_concat_id: 
    "\<lbrakk> Z \<notin> \<Union>set (map set ls) \<rbrakk> \<Longrightarrow> tokenize Z (concat_sep Z ls) = ls"
    by (induction ls) (auto simp: tokenize_NZZ)  
  *)
  
  subsubsection \<open>Simple Parser\<close>    
  text \<open>The parsing algorithm succeeds iff the input is non-empty and ends 
    with a zero. In case of success, it returns the tokenization of the input\<close>  
      
  text \<open>As a warm-up, we phrase the parser on lists. Our ultimate goal, 
    however, is to phrase the parser as a fold-operation on iterators.\<close>
    
  partial_function (option) tok_parser where
    "tok_parser Z l = (case l of 
      [] \<Rightarrow> Some [] 
    | [x] \<Rightarrow> if x=Z then Some [[]] else None
    | x#xs \<Rightarrow> if x=Z then do { ls \<leftarrow> tok_parser Z xs; Some ([]#ls) }
              else do { 
                ls \<leftarrow> tok_parser Z xs;
                case ls of l#ls \<Rightarrow> Some ((x#l)#ls) | _ \<Rightarrow> None
              }
    )"
    
  lemma tok_parser_some_eq: "tok_parser Z l = Some ls \<Longrightarrow> ls=tokenize Z l"
    apply (induction Z\<equiv>Z l arbitrary: ls rule: tokenize.induct)
    subgoal  
      by (subst (asm) tok_parser.simps) auto
    subgoal for x 
      by (subst (asm) tok_parser.simps) auto
    subgoal for x1 x2 xs ls
      apply (rewrite at "tok_parser Z (x1 # x2 # xs)" in asm tok_parser.simps)
      apply (auto split!: list.splits Option.bind_splits)
      done
    done    

      
  lemma tok_parser_undefined_iff: "tok_parser Z l = None \<longleftrightarrow> l\<noteq>[] \<and> last l \<noteq> Z"  
    apply (induction Z\<equiv>Z l rule: tokenize.induct)
    subgoal by (subst tok_parser.simps) (auto) 
    subgoal for x by (subst tok_parser.simps) (auto)
    subgoal for x1 x2 xs    
      apply (rewrite at "tok_parser Z (x1 # x2 # xs)" tok_parser.simps)
      apply (auto split!: list.splits Option.bind_splits if_splits)
      apply (auto dest!: tok_parser_some_eq)  
      by (metis last_ConsR list.simps(3) tokenize_not_empty)
    done  

  lemma tok_parser_defined_iff: 
    "tok_parser Z l = Some ls \<longleftrightarrow> (l=[] \<or> last l = Z) \<and> ls=tokenize Z l"
    by (metis not_None_eq tok_parser_some_eq tok_parser_undefined_iff)
      
      
  theorem tok_parser_correct: "case tok_parser Z l of 
    None \<Rightarrow> l\<noteq>[] \<and> last l \<noteq> Z
  | Some ls \<Rightarrow> (l=[] \<or> last l = Z) \<and> l = concat_sep Z ls"
    by (auto 
        split: option.split 
        simp: tok_parser_defined_iff tok_parser_undefined_iff concat_tokenize_id)
      
    
  subsection \<open>Parsing Fold over Tokenization\<close>  
  context iterator begin  
    
    definition tok_fold 
      :: "'it \<Rightarrow> 'it \<Rightarrow> ('it \<Rightarrow> 's \<Rightarrow> ('e,'it\<times>'s) enres) \<Rightarrow> 's \<Rightarrow> ('e,'s) enres" 
      where "tok_fold itE it f s \<equiv> doE {
        (_,s) \<leftarrow> EWHILEIT 
                  (\<lambda>(it,s). I it) (\<lambda>(it,s). it\<noteq>itE) (\<lambda>(it,s). f it s) (it,s);
        ERETURN s
      }"
    
    lemma tok_fold_rule:    
      assumes [simp]: "\<Phi> [] s"
      assumes SEG: "seg it l itE"  
      assumes F_RL: "\<And>ls s it. \<lbrakk> \<Phi> ls s; I it; it \<noteq> itE; itran it itE \<rbrakk> 
        \<Longrightarrow> f it s \<le> ESPEC E (\<lambda>(it',s'). \<exists>l. lz_string Z it l it' 
                                \<and> itran it' itE \<and> \<Phi> (ls@[l]) s')"
      assumes IMP_Q: "\<And>s. \<lbrakk> l\<noteq>[] \<longrightarrow> last l = Z; \<Phi> (tokenize Z l) s\<rbrakk> \<Longrightarrow> Q s"
      shows "tok_fold itE it f s \<le> ESPEC E Q"  
      unfolding tok_fold_def
      apply (refine_vcg 
            EWHILEIT_expinv_rule[where 
                  I="\<lambda>(it',s). \<exists>l. seg it l it' \<and> itran it' itE 
                                \<and> (l\<noteq>[] \<longrightarrow> last l = Z) \<and> \<Phi> (tokenize Z l) s"
              and R = "measure (\<lambda>(it',_). length (the_seg it' itE))"
            ]
          )
      apply (vc_solve)
      subgoal using SEG by (auto simp: itran_def)
      subgoal for ith s l
        apply (refine_vcg F_RL[THEN ESPEC_trans, refine_vcg])  
        apply assumption  
        apply (vc_solve)
        subgoal for it' s' l' 
          apply (rule exI[where x="l@l'@[Z]"]; intro conjI)
          subgoal by (metis (no_types, lifting) lz_string_def seg_concat)  
          applyS auto    
          applyS (auto simp: tokenize_append lz_string_noZ)
          done
        subgoal 
          by (metis Nil_is_append_conv itran_def itran_measure' lz_string_def 
              seg.simps(2) seg_eq_iff_empty seg_no_cyc)
        done
      subgoal using IMP_Q SEG seg_unique by blast
      done  
    
    lemma tok_fold_refine[refine]:    
      assumes [simplified, simp]: "(itEi,itE)\<in>Id" "(iti,it)\<in>Id"
      assumes R0: "(si,s)\<in>R"
      assumes STEP_REF: 
        "\<And>iti it si s. \<lbrakk> (iti,it)\<in>Id; (si,s)\<in>R; I it; it\<noteq>itE \<rbrakk> 
                      \<Longrightarrow> fi iti si \<le> \<Down>\<^sub>E E (Id \<times>\<^sub>r R) (f it s)"
      shows "tok_fold itEi iti fi si \<le> \<Down>\<^sub>E E R (tok_fold itE it f s)"
      unfolding tok_fold_def  
      apply (refine_rcg STEP_REF)
      apply (auto simp: R0)
      done  
        
    lemmas [enres_inline] = tok_fold_def
        
  end
    
    
  subsection \<open>Array Iterator\<close>  
  text \<open>We instantiate the abstract iterator interface for indexes 
    into an array.\<close>
    
  definition "ait_next (_::_ list) \<equiv> Suc"  
  definition "ait_peek \<equiv> nth"  
  definition "ait_begin (_::_ list) \<equiv> (1::nat)"  
  definition "ait_end \<equiv> length"  

  locale array_iterator =   
    fixes a :: "'a::heap list"
    (*assumes a_not_empty[simp]: "a\<noteq>[]"*)
  begin  
    definition "I it \<equiv> it>0 \<and> it\<le>length a" \<comment> \<open>Unused zero-position\<close>
    abbreviation "peek \<equiv> ait_peek a"
    abbreviation "next" where "next \<equiv> ait_next a"  
    abbreviation "begin" where "begin \<equiv> ait_begin a"
    abbreviation "end" where "end \<equiv> ait_end a"
      
    sublocale iterator I "next" peek by unfold_locales (auto simp: ait_next_def)
    
    lemma I_begin[simp, intro!]: "a\<noteq>[] \<Longrightarrow> I begin" 
      by (auto simp: I_def ait_begin_def)
    lemma I_end[simp, intro!]: "a\<noteq>[] \<Longrightarrow> I end" 
      by (auto simp: I_def ait_end_def)
        
    definition "a_assn a' p \<equiv> p \<mapsto>\<^sub>a a' * \<up>(a'=a \<and> a\<noteq>[])"
    definition "it_assn \<equiv> b_assn nat_assn I"  

    lemma it_assn_pure[safe_constraint_rules]: "CONSTRAINT is_pure it_assn" 
      unfolding it_assn_def by solve_constraint
      
    lemma it_assn_unused[safe_constraint_rules]: 
      "CONSTRAINT (is_unused_elem 0) it_assn" 
      by (auto simp: is_unused_elem_def it_assn_def pure_def I_def)
      
    lemma a_assn_rdompD: "rdomp a_assn a' \<Longrightarrow> a'=a"
      unfolding a_assn_def
      by (auto simp: rdomp_def)
        
    lemma next_refine[sepref_fr_rules]: 
      "(uncurry (return oo (\<lambda>_. (+) 1)), uncurry (RETURN oo ait_next)) 
        \<in> [\<lambda>(_,it). it\<noteq>end]\<^sub>a a_assn\<^sup>k *\<^sub>a it_assn\<^sup>k \<rightarrow> it_assn"
      unfolding it_assn_def
      apply sepref_to_hoare
      apply (sep_auto simp: ait_end_def I_def ait_next_def)
      done  
        
    lemma peek_refine[sepref_fr_rules]: 
      "(uncurry Array.nth, uncurry (RETURN oo ait_peek)) 
      \<in> [\<lambda>(_,it). it\<noteq>end]\<^sub>a a_assn\<^sup>k *\<^sub>a it_assn\<^sup>k \<rightarrow> id_assn"
      unfolding it_assn_def a_assn_def
      apply sepref_to_hoare
      apply (sep_auto simp: I_def ait_end_def ait_peek_def)
      done  

    lemma begin_refine[sepref_fr_rules]: 
      "(\<lambda>_. return 1, RETURN o ait_begin) \<in> a_assn\<^sup>k \<rightarrow>\<^sub>a it_assn" 
      unfolding it_assn_def a_assn_def
      apply sepref_to_hoare
      apply (sep_auto simp: I_def ait_begin_def)
      done
        
    lemma end_refine[sepref_fr_rules]:
      "(Array.len, RETURN o ait_end) \<in> a_assn\<^sup>k \<rightarrow>\<^sub>a it_assn"
      unfolding it_assn_def a_assn_def
      apply sepref_to_hoare
      apply (sep_auto simp: I_def ait_end_def)
      done  
      
    lemma it_assn_eq_impl[sepref_fr_rules]: 
      "(uncurry (return oo (=)),uncurry (RETURN oo (=))) 
      \<in> it_assn\<^sup>k *\<^sub>a it_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
      unfolding it_assn_def
      apply sepref_to_hoare
      apply sep_auto
      done  

    lemma begin_less_end[simp]: "begin \<le> end \<longleftrightarrow> a\<noteq>[]" 
      unfolding ait_begin_def ait_end_def by auto
   
    lemma itran_alt: "itran it it' \<longleftrightarrow> begin\<le>it \<and> it \<le> it' \<and> it' \<le> end"
      unfolding ait_begin_def ait_end_def
      apply (rule iffI; clarsimp)    
      subgoal by (auto simp: I_def itran_ord dest: itran_invar)  
      subgoal proof -
        assume
          "it \<le> it'"
          "Suc 0 \<le> it"
          "it' \<le> length a"
        thus "itran it it'" 
          apply (induction rule: dec_induct)
          subgoal by (auto simp: I_def)
          subgoal for ith
            using itran_next2I
            unfolding ait_next_def  
            apply (auto simp: I_def)
            done
          done
      qed
      done  
        
    lemma seg_is_slice:
      assumes "seg it l it'"
      shows "l = slice it it' a"
      using assms  
      apply (induction l arbitrary: it)
      applyS (auto)
      apply clarsimp  
      apply (rewrite in "seg \<hole>" in asm ait_next_def)  
      apply (rewrite in "peek _ # _" ait_peek_def) (* TODO: Clean up proof *)
    proof -
      fix la :: "'a list" and ita :: nat
      assume a1: "seg (Suc ita) la it'"
      assume a2: "\<And>it. seg it la it' \<Longrightarrow> la = slice it it' a"
    have f3: "\<forall>n na nb. \<not> (n::nat) \<le> na \<or> \<not> nb < n \<or> nb < na"
      using dual_order.strict_trans1 by blast
      have f4: "Suc ita \<le> it'"
        using a1 seg_ord by blast
    then have f5: "ita < it'"
      using f3 by blast
      have f6: "\<forall>n na. \<not> (n::nat) < na \<and> n \<noteq> na \<or> n \<le> na"
        using less_or_eq_imp_le by blast
      then have f7: "ita \<le> Suc ita"
        by (meson lessI)
      have "length (take it' a) \<le> ita \<longrightarrow> drop (Suc ita) (take it' a) \<noteq> []"
    using f6 f4 f3 a1 by (metis (no_types) I_def Misc.slice_def antisym_conv2 diff_diff_cancel drop_all drop_take lessI seg_invar2 slice_len)
    then have "\<not> length (take it' a) \<le> ita"
      using f7 f6 f3 by (metis (no_types) antisym_conv2 drop_all)
      then show "a ! ita # la = slice ita it' a"
        using f5 a2 a1 by (metis (no_types) Cons_nth_drop_Suc I_def Misc.slice_def drop_take hd_drop_conv_nth leI seg_invar2 slice_head)
    qed
        
    lemma seg_exists:
      "\<lbrakk> 0<it; it\<le>it'; it'\<le>length a \<rbrakk> \<Longrightarrow> \<exists>l. seg it l it'"
      by (metis I_def ait_end_def itran_alt itran_def itran_refl order_trans)
  
    lemma seg_sliceI: 
      "\<lbrakk> 0<it; it\<le>it'; it'\<le>length a \<rbrakk> \<Longrightarrow> seg it (slice it it' a) it'"    
      apply (drule (2) seg_exists)
      apply (clarify)  
      apply (frule seg_is_slice)
      by simp  
        
    
    lemma seg_slice_conv: 
      "seg it l it' \<longleftrightarrow> 0<it \<and> it\<le>it' \<and> it'\<le>length a \<and> l = slice it it' a"
      by (auto 
            simp: seg_sliceI seg_ord I_def seg_is_slice 
            dest: seg_invar1 seg_invar2)
        
        
  end  

  sepref_register ait_next ait_peek ait_begin ait_end
    

end
