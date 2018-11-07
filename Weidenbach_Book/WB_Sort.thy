theory WB_Sort
  imports
    WB_More_Refinement
begin

definition partition_between where
  \<open>partition_between i j xs = do {
     ASSERT(i \<le> length xs \<and> j \<le> length xs);
     pivot \<leftarrow> RETURN (xs ! i);
     (i, j, xs) \<leftarrow> WHILE\<^sub>T
       (\<lambda>(i, j, xs). i \<le> j)
       (\<lambda>(i, j, xs). do {
          i \<leftarrow> WHILE\<^sub>T(\<lambda>i. xs ! i < pivot)
            (\<lambda>i. RETURN (i+1))
	    i;
          j \<leftarrow> WHILE\<^sub>T(\<lambda>j. xs ! j \<ge> pivot)
                (\<lambda>j. RETURN (j-1))
	        j;
	  let xs = (if (i < j) then swap xs i j else xs);
	  RETURN (i, j, xs)
       })
       (i,j, xs);
     RETURN (xs, j)
   }\<close>

term RECT
definition quicksort :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'a::ord list \<Rightarrow> 'a list nres\<close> where
\<open>quicksort i j xs =
  RECT (\<lambda>f (i,j,xs). do {
      if i \<ge> j then RETURN xs
      else do {
	(xs, k) \<leftarrow> partition_between i j xs;
	xs \<leftarrow> f (i, k, xs);
	f (k+1, j, xs)
      }
    })
    (i, j, xs)\<close>
find_theorems trimono
thm trimonoI'
lemma "quicksort 0 2 [(0::nat), (5::nat), (1::nat)] = A"
proof -
  have \<open>trimono (\<lambda>f (i, j, xs).
         if j \<le> i then RETURN xs else do {
                                        (xs, k) \<leftarrow> partition_between i j xs;
xs \<leftarrow> f (i, k, xs);
f (k + 1, j, xs)
                                      })\<close>
    apply (rule trimonoI')
    apply (auto simp: monotone_def fun_ord_def)
    sorry
				      
  show ?thesis
  apply (simp add: quicksort_def partition_between_def RECT_unfold)
  apply (subst RECT_unfold)
  
  apply (simp add: trimono_def)
  
end