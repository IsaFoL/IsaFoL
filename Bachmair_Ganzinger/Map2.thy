theory Map2 imports Main begin

(* Definition is from "$AFP/Jinja/DFA/Listn.thy" *)
definition map2 :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list"
where
  "map2 f = (\<lambda>xs ys. map (case_prod f) (zip xs ys))"


lemma map2_empty[simp]: "map2 f [] [] = []" oops
   
lemma length_map2[simp]:
  "length t = length s \<Longrightarrow> length (map2 f s t) = length s" oops
    
lemma inj_map2[iff]: "inj (map2 f) = inj f" oops
    
end