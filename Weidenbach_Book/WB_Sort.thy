theory WB_Sort
  imports
    WB_More_Refinement
begin

definition partition_between :: \<open>('b \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> ('a list \<times> nat) nres\<close> where
  \<open>partition_between R h i j xs = do {
     ASSERT(i \<le> length xs \<and> j \<le> length xs);
     pivot \<leftarrow> RETURN (h (xs ! i));
     (i, j, xs) \<leftarrow> WHILE\<^sub>T
       (\<lambda>(i, j, xs). i < j)
       (\<lambda>(i, j, xs). do {
          i \<leftarrow> WHILE\<^sub>T(\<lambda>i. R (h (xs ! i)) pivot \<and> i < j)
            (\<lambda>i. RETURN (i+1))
	    i;
          j \<leftarrow> WHILE\<^sub>T(\<lambda>j. R pivot (h (xs ! j)) \<and> j > i)
                (\<lambda>j. RETURN (j-1))
	        j;
	  let xs = (if (i < j) then swap xs i j else xs);
	  RETURN (i, j, xs)
       })
       (i,j, xs);
     RETURN (xs, j)
   }\<close>


definition quicksort :: \<open>_ \<Rightarrow> _ \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a::ord list \<Rightarrow> 'a list nres\<close> where
\<open>quicksort R h i j xs = do {
  RECT (\<lambda>f (i,j,xs). do {
      if i \<ge> j then RETURN xs
      else do{
	(xs, k) \<leftarrow> partition_between R h i j xs;
	xs \<leftarrow> f (i, k, xs);
	f (k+1, j, xs)
      }
    })
    (i, j, xs)
  }\<close>

lemma "quicksort (<) id 0 3 [(0::nat), (5::nat), (1::nat), 2] = A"
proof -
				      
  show ?thesis
    unfolding quicksort_def partition_between_def
    apply (simp add: quicksort_def partition_between_def RECT_unfold)
    apply (subst RECT_unfold, refine_mono, simp add: WHILEIT_unfold)
  apply (subst WHILET_unfold, simp)
  apply (subst WHILET_unfold, simp)
  apply (subst WHILET_unfold, simp)
  apply (subst WHILET_unfold, simp)
  apply (subst WHILET_unfold, simp)
  apply (subst WHILET_unfold, simp)
    apply (subst RECT_unfold, refine_mono)
    apply (simp add: )
    apply (subst RECT_unfold, refine_mono)
    apply (simp add: WHILET_unfold)
    apply (subst RECT_unfold, refine_mono)
    apply (simp add: WHILET_unfold)
    apply (subst RECT_unfold, refine_mono)
    apply (simp add: WHILET_unfold)
    apply (subst RECT_unfold, refine_mono)
    apply (simp add: WHILET_unfold)
    apply (subst RECT_unfold, refine_mono)
    apply (simp add: WHILET_unfold)
    apply (subst RECT_unfold, refine_mono)
    apply (simp add: WHILET_unfold)
    apply (subst RECT_unfold, refine_mono)
    apply (simp add: WHILET_unfold)
    apply (simp add: swap_def)
  oops
end