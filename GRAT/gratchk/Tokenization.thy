theory Tokenization
imports "Automatic_Refinement.Misc"
begin

  section \<open>Tokenization\<close>  
  text \<open>We first define a function that joins a list of lists, 
    terminating each sublist by a zero.\<close>
  primrec concat_sep :: "'a \<Rightarrow> 'a list list \<Rightarrow> 'a list" where
    "concat_sep Z [] = []"
  | "concat_sep Z (l#ls) = l @ Z # concat_sep Z ls"  
    
  lemma concat_sep_empty_iff[simp]: "concat_sep Z ls = [] \<longleftrightarrow> ls=[]"  
    by (cases ls) auto
    
  lemma concat_sep_by_concat_map: 
    "concat_sep Z ll = concat (map (\<lambda>l . l@[Z]) ll)"
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
    assumes "Z \<notin> \<Union>(set (map set ls1))" 
    assumes "Z \<notin> \<Union>(set (map set ls2))" 
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
    "\<lbrakk>l\<noteq>[] \<longrightarrow> last l = Z\<rbrakk> \<Longrightarrow> Z \<notin> \<Union>(set (map set (tokenize Z l)))"
    by (induction l rule: tokenize.induct) (auto split: list.splits)

  lemma tokenize_complete_set: 
    "\<lbrakk> ll\<noteq>[] \<longrightarrow> last ll = Z; l \<in> set (tokenize Z ll); x\<in>set l \<rbrakk> \<Longrightarrow> x\<noteq>Z"  
    by (drule tokenize_complete) auto  
      
      
  lemma unique_tokenization: 
    "\<lbrakk> l\<noteq>[] \<longrightarrow> last l = Z \<rbrakk> 
    \<Longrightarrow> \<exists>!ls. (Z\<notin>\<Union>(set (map set ls)) \<and> concat_sep Z ls = l)"
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
    \<Longrightarrow> tokenize Z l = (THE ls. Z\<notin>\<Union>(set (map set ls)) \<and> concat_sep Z ls = l)"
    apply (frule theI'[OF unique_tokenization])
    by (metis (no_types, lifting) concat_sep_unique concat_tokenize_id 
              tokenize_complete)
      
      
  lemma unique_tokenize_presentation:              
    assumes "l\<noteq>[] \<longrightarrow> last l = Z"
    shows "\<exists>!ls. (Z\<notin>\<Union>(set (map set ls)) \<and> concat_sep Z ls = l)"
      and "tokenize Z l = (THE ls. Z\<notin>\<Union>(set (map set ls)) \<and> concat_sep Z ls = l)"
      using unique_tokenization[OF assms] tokenize_spec[OF assms] .
              
  lemma tokenize_concat_id: 
    "\<lbrakk> Z \<notin> \<Union>(set (map set ls)) \<rbrakk> \<Longrightarrow> tokenize Z (concat_sep Z ls) = ls"
    by (induction ls) (auto simp: tokenize_NZZ)  


end
