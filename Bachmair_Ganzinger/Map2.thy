theory Map2 imports Main begin

abbreviation image2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a * 'b) set \<Rightarrow> 'c set" where
  "image2 f s \<equiv> (case_prod f) ` s"
  
  
  
(* Definition is from "$AFP/Jinja/DFA/Listn.thy" *)
definition map2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list"
where
  "map2 f = (\<lambda>xs ys. map (case_prod f) (zip xs ys))"
  
lemma map2_length[simp]: "length (map2 f as bs) = min (length as) (length bs)"
  unfolding map2_def by auto

lemma map2_empty_r[simp]: "map2 f [] ys = []"
  unfolding map2_def by auto
    
lemma map2_empty_l[simp]: "map2 f [] xs = []"
  unfolding map2_def by auto
   
lemma length_map2[simp]:
  "length t = length s \<Longrightarrow> length (map2 f s t) = length s"
  unfolding map2_def by (induction t arbitrary: s) auto
      
lemma image_map2: "length t = length s \<Longrightarrow> 
         g ` set (map2 f t s) = set (map2 (\<lambda>a b. g (f a b)) t s)"
  unfolding map2_def by (induction t arbitrary: s) auto
  
lemma inj_map2[iff]: "inj (map2 f) = inj f" oops
    
lemma map2_nth[simp]: "length t = length s \<Longrightarrow> i < length s \<Longrightarrow> (map2 f s t) ! i = f (s!i) (t!i)"
  unfolding map2_def by (induction t arbitrary: s) auto
    
    
lemma map2_tl: "length t = length s \<Longrightarrow> (map2 f (tl t) (tl s)) = tl (map2 f (t) (s))"  
  unfolding map2_def apply (induction t arbitrary: s)
   apply auto
  by (smt Suc_length_conv list.sel(3) list.simps(9) zip_Cons_Cons)
    
lemma map2_Cons[simp]: "map2 f (x # xs) (y # ys) = f x y # map2 f xs ys"
  unfolding map2_def
    by auto



    
    
end