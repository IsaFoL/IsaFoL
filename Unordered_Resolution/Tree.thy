theory Tree imports Main begin

(* Sometimes it is nice to think of bool's as directions in a binary tree *)
hide_const (open) Left Right
type_synonym dir = bool
definition Left :: bool where "Left = True"
definition Right :: bool where "Right = False"
declare Left_def [simp]
declare Right_def [simp]

(* hide_const (open) Leaf Branch *)
datatype tree =
  Leaf
| Branch (ltree: tree) (rtree: tree)

section {* Sizes *}

fun treesize :: "tree \<Rightarrow> nat" where
  "treesize Leaf = 0"
| "treesize (Branch l r) = 1 + treesize l + treesize r"

lemma treesize_Leaf: "treesize T = 0 \<Longrightarrow> T=Leaf" by (cases T) auto

lemma treesize_Branch: "treesize T = Suc n \<Longrightarrow> \<exists>l r. T=Branch l r" by (cases T) auto


section {* Paths *}

inductive path :: "dir list \<Rightarrow> tree \<Rightarrow> bool" where
  "path [] t"
| "path ds l \<Longrightarrow> path (Left#ds) (Branch l r) "
| "path ds r \<Longrightarrow> path (Right#ds) (Branch l r)"
(* I could use anonymous variable *)



lemma path_inv_Leaf: "path p Leaf \<longleftrightarrow> p = []"
apply auto
using path.simps apply blast
apply (simp add: path.intros)
done

lemma path_inv_Branch_Left:  
  "path (Left#p) (Branch l r) \<longleftrightarrow> path p l"
using path.intros apply auto
using Left_def Right_def path.cases apply blast
done

lemma path_inv_Branch_Right: 
  "path (Right#p) (Branch l r) \<longleftrightarrow> path p r"
using path.intros apply auto
using Left_def Right_def path.cases apply blast
done

lemma path_inv_Branch: 
  "path p (Branch l r) \<longleftrightarrow> (p=[] \<or> (\<exists>a p'. p=a#p'\<and> (a \<longrightarrow> path p' l) \<and> (\<not>a \<longrightarrow> path p' r)))" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L then show ?R using path.simps[of p] by auto
next
  assume r: ?R
  then show ?L
    proof
      assume "p = []" then show ?L using path.intros by auto
    next
      assume "\<exists>a p'. p=a#p'\<and> (a \<longrightarrow> path p' l) \<and> (\<not>a \<longrightarrow> path p' r)"
      then obtain a p' where "p=a#p'\<and> (a \<longrightarrow> path p' l) \<and> (\<not>a \<longrightarrow> path p' r)" by auto
      then show ?L using path.intros by (cases a) auto
    qed
qed

lemma path_prefix: "path (ds1@ds2) T \<Longrightarrow> path ds1 T"
proof (induction ds1 arbitrary: T)
  case (Cons a ds1)
  then have "\<exists>l r. T = Branch l r" sorry
  then obtain l r where p_lr: "T = Branch l r" by auto
  show ?case
    proof (cases a)
      assume atrue: "a"
      then have "path ((ds1) @ ds2) l" using p_lr Cons(2) path_inv_Branch by auto
      then have "path ds1 l" using Cons(1) by auto
      then show "path (a # ds1) T" using p_lr path.intros atrue by auto
    next
      assume afalse: "~a"
      then have "path ((ds1) @ ds2) r" using p_lr Cons(2) path_inv_Branch by auto
      then have "path ds1 r" using Cons(1) by auto
      then show "path (a # ds1) T" using p_lr path.intros afalse by auto
    qed
next
  case (Nil) then show ?case using path.intros by auto
qed
      
section {* Branches *}

inductive branch :: "dir list \<Rightarrow> tree \<Rightarrow> bool" where
  "branch [] Leaf"    
| "branch ds l \<Longrightarrow> branch (Left # ds) (Branch l r)"
| "branch ds r \<Longrightarrow> branch (Right # ds) (Branch l r)"

lemma has_branch: "\<exists>b. branch b T"
proof (induction T)
  case (Leaf) then show ?case using branch.intros by auto
next
  case (Branch T\<^sub>1 T\<^sub>2)
  then obtain b where "branch b T\<^sub>1" by auto
  then have "branch (Left#b) (Branch T\<^sub>1 T\<^sub>2)" using branch.intros by auto
  then show ?case by auto
qed

lemma branch_inv_Leaf: "branch b Leaf \<longleftrightarrow> b = []" using branch.simps by blast

lemma branch_inv_Branch_Left:  
  "branch (Left#b) (Branch l r) \<longleftrightarrow> branch b l"
using branch.intros apply auto
using Left_def Right_def branch.cases apply blast
done

lemma branch_inv_Branch_Right: 
  "branch (Right#b) (Branch l r) \<longleftrightarrow> branch b r"
using branch.intros apply auto
using Left_def branch.cases by blast

lemma branch_inv_Branch: 
  "branch b (Branch l r) \<longleftrightarrow> 
     (\<exists>a b'. b=a#b'\<and> (a \<longrightarrow> branch b' l) \<and> (\<not>a \<longrightarrow>  branch b' r))"
using branch.simps[of b] by auto

lemma branch_inv_Leaf2:
  "T=Leaf \<longleftrightarrow> (\<forall>b. branch b T \<longrightarrow> b=[])"
proof -
  {
    assume "T=Leaf"
    then have "\<forall>b. branch b T \<longrightarrow> b = []" using branch_inv_Leaf by auto
  }
  moreover 
  {
    assume "\<forall>b. branch b T \<longrightarrow> b=[]"
    then have "\<forall>b. branch b T \<longrightarrow> \<not>(\<exists>a b'. b = a # b')" by auto
    then have "\<forall>b. branch b T \<longrightarrow> \<not>(\<exists>l r. branch b (Branch l r))" 
      using branch_inv_Branch by auto
    then have "T=Leaf" using has_branch[of T]  by (metis branch.simps)
  }
  ultimately show "T=Leaf \<longleftrightarrow> (\<forall>b. branch b T \<longrightarrow> b=[])" by auto
qed

lemma branch_is_path: 
  "branch ds T \<Longrightarrow> path ds T"
proof (induction T arbitrary: ds)
  case Leaf
  then have "ds = []" using branch_inv_Leaf by auto
  then show ?case using path.intros by auto
next
  case (Branch T\<^sub>1 T\<^sub>2) 
  then obtain a b where ds_p: "ds = a # b \<and> (a \<longrightarrow> branch b T\<^sub>1) \<and> (\<not> a \<longrightarrow> branch b T\<^sub>2)" using branch_inv_Branch[of ds] by blast
  then have "(a \<longrightarrow> path b T\<^sub>1) \<and> (\<not>a \<longrightarrow> path b T\<^sub>2)" using Branch by auto
  then show "?case" using ds_p path.intros by (cases a) auto
qed

lemma Branch_Leaf_Leaf_Tree: "(T = Branch l r \<longrightarrow> (\<exists>B. branch (B@[True]) T \<and> branch (B@[False]) T)) \<and> (T=Leaf \<longrightarrow> branch [] T )"
proof (induction T arbitrary: l r)
  case Leaf then show ?case using branch.intros by auto
next
  case (Branch T1 T2) 
  then show ?case
    apply (cases T1)
    apply (cases T2)
    apply auto
      proof -
        have "branch ([] @ [True]) (Branch Leaf Leaf) \<and> branch ([] @ [False]) (Branch Leaf Leaf)" using branch.intros by auto
        then show "\<exists>B. branch (B @ [True]) (Branch Leaf Leaf) \<and> branch (B @ [False]) (Branch Leaf Leaf)" by blast
      next
        fix x21 x22
        assume "(\<And>l r. x21 = l \<and> x22 = r \<longrightarrow>  (\<exists>B. branch (B @ [True]) (Branch l r) \<and> branch (B @ [False]) (Branch l r)))"
        then have "\<exists>B'. branch (B' @ [True]) (Branch x21 x22) \<and> branch (B' @ [False]) (Branch x21 x22)" by blast
        then obtain B' where "branch (B' @ [True]) (Branch x21 x22) \<and> branch (B' @ [False]) (Branch x21 x22)" by auto
        then have "branch (False # (B' @ [True])) (Branch Leaf (Branch x21 x22)) \<and> branch (False # (B' @ [False])) (Branch Leaf (Branch x21 x22))" 
          using branch.intros(3)[of "B' @ [True]" "(Branch x21 x22)" "Leaf"] 
                branch.intros(3)[of "B' @ [False]" "(Branch x21 x22)" "Leaf"] by auto
        then have "branch ((False # B') @ [True]) (Branch Leaf (Branch x21 x22)) \<and> branch ((False # B') @ [False]) (Branch Leaf (Branch x21 x22))" by auto
        then show "\<exists>B. branch (B @ [True]) (Branch Leaf (Branch x21 x22)) \<and> branch (B @ [False]) (Branch Leaf (Branch x21 x22))" by metis
      next
        fix x21 x22
        assume "(\<And>l r. x21 = l \<and> x22 = r \<longrightarrow>   (\<exists>B. branch (B @ [True]) (Branch l r) \<and> branch (B @ [False]) (Branch l r)))"
        then have "(\<exists>B. branch (B @ [True]) (Branch x21 x22) \<and> branch (B @ [False]) (Branch x21 x22))" by auto
        then obtain B' where "branch (B' @ [True]) (Branch x21 x22) \<and> branch (B' @ [False]) (Branch x21 x22)" by auto
        then have "branch (True # (B' @ [True])) (Branch (Branch x21 x22) r) \<and> branch (True # (B' @ [False])) (Branch (Branch x21 x22) r) " 
          using branch.intros(2)[of "B' @ [True]" "(Branch x21 x22)" "r"] 
                branch.intros(2)[of "B' @ [False]" "(Branch x21 x22)" "r"] by auto
        then have "branch ((True # B') @ [True]) (Branch (Branch x21 x22) r) \<and> branch ((True # B') @ [False]) (Branch (Branch x21 x22) r) " by auto
        then show "\<exists>B. branch (B @ [True]) (Branch (Branch x21 x22) r) \<and>
           branch (B @ [False]) (Branch (Branch x21 x22) r)" by metis
      qed qed

section {* Internal Nodes *}

inductive internal :: "dir list \<Rightarrow> tree \<Rightarrow> bool" where
  "internal [] (Branch l r)"
| "internal ds l \<Longrightarrow> internal (Left#ds) (Branch l r) "
| "internal ds r \<Longrightarrow> internal (Right#ds) (Branch l r)"
(* Could use anonymous var in first case *)

lemma internal_inv_Leaf: "\<not>internal b Leaf" using internal.simps by blast

lemma internal_inv_Branch_Left:  
  "internal (Left#b) (Branch l r) \<longleftrightarrow> internal b l"
apply rule
using internal.intros apply auto
using Left_def Right_def internal.cases apply blast
done

lemma internal_inv_Branch_Right: 
  "internal (Right#b) (Branch l r) \<longleftrightarrow> internal b r"
using internal.intros apply auto
using Left_def Right_def internal.cases apply blast
done

lemma internal_inv_Branch: 
  "internal p (Branch l r) \<longleftrightarrow> (p=[] \<or> (\<exists>a p'. p=a#p'\<and> (a \<longrightarrow> internal p' l) \<and> (\<not>a \<longrightarrow> internal p' r)))" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L then show ?R using internal.simps[of p] by auto
next
  assume r: ?R
  then show ?L
    proof
      assume "p = []" then show ?L using internal.intros by auto
    next
      assume "\<exists>a p'. p=a#p'\<and> (a \<longrightarrow> internal p' l) \<and> (\<not>a \<longrightarrow> internal p' r)"
      then obtain a p' where "p=a#p'\<and> (a \<longrightarrow> internal p' l) \<and> (\<not>a \<longrightarrow> internal p' r)" by auto
      then show ?L using internal.intros by (cases a) auto
    qed
qed

lemma internal_is_path: 
  "internal ds T \<Longrightarrow> path ds T"
proof (induction T arbitrary: ds)
  case Leaf
  then have "False" using internal_inv_Leaf by auto
  then show ?case by auto
next
  case (Branch T\<^sub>1 T\<^sub>2) 
  then obtain a b where ds_p: "ds=[] \<or> ds = a # b \<and> (a \<longrightarrow> internal b T\<^sub>1) \<and> (\<not> a \<longrightarrow> internal b T\<^sub>2)" using internal_inv_Branch by blast
  then have "ds = [] \<or> (a \<longrightarrow> path b T\<^sub>1) \<and> (\<not>a \<longrightarrow> path b T\<^sub>2)" using Branch by auto
  then show "?case" using ds_p path.intros by (cases a) auto
qed

fun parent :: "dir list \<Rightarrow> dir list" where
  "parent ds = tl ds"

abbreviation prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "prefix a b \<equiv> \<exists>c. a @ c = b" 

abbreviation pprefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "pprefix a b \<equiv> \<exists>c. a @ c = b \<and> a\<noteq>b" 

abbreviation postfix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "postfix a b \<equiv> \<exists>c. c @ a = b"

abbreviation ppostfix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "ppostfix a b \<equiv> \<exists>c. c @ a = b \<and> a\<noteq>b"

section {* Deleting Nodes *}

fun delete :: "dir list \<Rightarrow> tree \<Rightarrow> tree" where
  "delete [] T = Leaf"
| "delete (True#ds)  (Branch T\<^sub>1 T\<^sub>2) = Branch (delete ds T\<^sub>1) T\<^sub>2"
| "delete (False#ds) (Branch T\<^sub>1 T\<^sub>2) = Branch T\<^sub>1 (delete ds T\<^sub>2)"
(* First case could use anonymous variable*) (* Red could also be defined as a tree, i.e. a dir list set *)

fun cutoff :: "(dir list \<Rightarrow> bool) \<Rightarrow> dir list \<Rightarrow> tree \<Rightarrow> tree" where
  "cutoff red ds (Branch T\<^sub>1 T\<^sub>2) = 
     (if red ds then Leaf else Branch (cutoff red (ds@[Left])  T\<^sub>1) (cutoff red (ds@[Right]) T\<^sub>2))"
| "cutoff red ds Leaf = Leaf"
(* Hvis alle branches er røde, så giver cut_off et subtree *)(* Hvis alle branches er røde, så gælder det sammme for cut_off *)(* Alle interne stier er ikke røde *)

abbreviation anypath :: "tree \<Rightarrow> (dir list \<Rightarrow> bool) \<Rightarrow> bool" where
  "anypath T P \<equiv> \<forall>p. path p T \<longrightarrow> P p"

abbreviation anybranch :: "tree \<Rightarrow> (dir list \<Rightarrow> bool) \<Rightarrow> bool" where
  "anybranch T P \<equiv> \<forall>p. branch p T \<longrightarrow> P p"

abbreviation anyinternal :: "tree \<Rightarrow> (dir list \<Rightarrow> bool) \<Rightarrow> bool" where
  "anyinternal T P \<equiv> \<forall>p. internal p T \<longrightarrow> P p"

lemma cutoff_branch': 
  "anybranch T (\<lambda>b. red(ds@b)) \<Longrightarrow> anybranch (cutoff red ds T) (\<lambda>b. red(ds@b))"
proof (induction T arbitrary: ds) (* This proof seems a bit excessive for such a simple theorem *)
  case (Leaf) 
  let ?T = "cutoff red ds Leaf"
  {
    fix b
    assume "branch b ?T"
    then have "branch b Leaf" by auto
    then have "red(ds@b)" using Leaf by auto
  }
  then show ?case by simp
next
  case (Branch T\<^sub>1 T\<^sub>2)
  let ?T = "cutoff red ds (Branch T\<^sub>1 T\<^sub>2)"
  from Branch have "\<forall>p. branch (Left#p) (Branch T\<^sub>1 T\<^sub>2) \<longrightarrow> red (ds @ (Left#p))" by blast
  then have "\<forall>p. branch p T\<^sub>1 \<longrightarrow> red (ds @ (Left#p))" using branch.intros by auto
  then have "anybranch T\<^sub>1 (\<lambda>p. red ((ds @ [Left]) @ p))"  using branch.intros by auto
  then have aa: "anybranch (cutoff red (ds @ [Left]) T\<^sub>1) (\<lambda>p. red ((ds @ [Left]) @ p)) 
         " using Branch by blast

  from Branch have "\<forall>p. branch (Right#p) (Branch T\<^sub>1 T\<^sub>2) \<longrightarrow> red (ds @ (Right#p))" by blast
  then have "\<forall>p. branch p T\<^sub>2 \<longrightarrow> red (ds @ (Right#p))" using branch.intros by auto
  then have "anybranch T\<^sub>2 (\<lambda>p. red ((ds @ [Right]) @ p))"  using branch.intros by auto
  then have bb: "anybranch (cutoff red (ds @ [Right]) T\<^sub>2) (\<lambda>p. red ((ds @ [Right]) @ p)) 
         " using Branch by blast
  {           
    fix b
    assume b_p: "branch b ?T"
    have "red ds \<or> \<not>red ds" by auto
    then have "red(ds@b)"
      proof
        assume ds_p: "red ds"
        then have "?T = Leaf" by auto
        then have "b = []" using b_p branch_inv_Leaf by auto
        then show "red(ds@b)" using ds_p by auto
      next
        assume ds_p: "\<not>red ds"
        let ?T\<^sub>1' = "cutoff red (ds@[Left])  T\<^sub>1"
        let ?T\<^sub>2' = "cutoff red (ds@[Right]) T\<^sub>2"
        from ds_p have "?T = Branch ?T\<^sub>1' ?T\<^sub>2'" by auto
        from this b_p obtain a b' where "b = a # b' \<and> (a \<longrightarrow> branch b' ?T\<^sub>1') \<and> (\<not>a \<longrightarrow> branch b' ?T\<^sub>2' )" using branch_inv_Branch[of b ?T\<^sub>1' ?T\<^sub>2'] by auto
        then show "red(ds@b)" using aa bb by (cases a) auto
      qed
  }
  then show ?case by blast
qed

lemma cutoff_branch: "anybranch T (\<lambda>p. red p) \<Longrightarrow> anybranch (cutoff red [] T) (\<lambda>p. red p)" 
  using cutoff_branch'[of T red "[]"] by auto

lemma cutoff_internal': 
  "anybranch T (\<lambda>b. red(ds@b)) \<Longrightarrow> anyinternal (cutoff red ds T) (\<lambda>b. \<not>red(ds@b))"
proof (induction T arbitrary: ds) (* This proof seems a bit excessive for such a simple theorem *)
  case (Leaf) then show ?case using internal_inv_Leaf by simp
next                                                     
  case (Branch T\<^sub>1 T\<^sub>2)
  let ?T = "cutoff red ds (Branch T\<^sub>1 T\<^sub>2)"
  from Branch have "\<forall>p. branch (Left#p) (Branch T\<^sub>1 T\<^sub>2) \<longrightarrow> red (ds @ (Left#p))" by blast
  then have "\<forall>p. branch p T\<^sub>1 \<longrightarrow> red (ds @ (Left#p))" using branch.intros by auto
  then have "anybranch T\<^sub>1 (\<lambda>p. red ((ds @ [Left]) @ p))"  using branch.intros by auto
  then have aa: "anyinternal (cutoff red (ds @ [Left]) T\<^sub>1) (\<lambda>p. \<not> red ((ds @ [Left]) @ p))" using Branch by blast

  from Branch have "\<forall>p. branch (Right#p) (Branch T\<^sub>1 T\<^sub>2) \<longrightarrow> red (ds @ (Right#p))" by blast
  then have "\<forall>p. branch p T\<^sub>2 \<longrightarrow> red (ds @ (Right#p))" using branch.intros by auto
  then have "anybranch T\<^sub>2 (\<lambda>p. red ((ds @ [Right]) @ p))"  using branch.intros by auto
  then have bb: "anyinternal (cutoff red (ds @ [Right]) T\<^sub>2) (\<lambda>p. \<not> red ((ds @ [Right]) @ p))" using Branch by blast
  {
    fix p
    assume b_p: "internal p ?T"
    then have ds_p: "\<not>red ds" using internal_inv_Leaf internal.intros by auto
    have "p=[] \<or> p\<noteq>[]" by auto
    then have "\<not>red(ds@p)"
      proof
        assume "p=[]" then show "\<not>red(ds@p)" using ds_p by auto
      next
        let ?T\<^sub>1' = "cutoff red (ds@[Left])  T\<^sub>1"
        let ?T\<^sub>2' = "cutoff red (ds@[Right]) T\<^sub>2"
        assume "p\<noteq>[]"
        moreover
        have "?T = Branch ?T\<^sub>1' ?T\<^sub>2'" using ds_p by auto
        ultimately
        obtain a p' where b_p: "p = a # p' \<and>
             (a \<longrightarrow> internal p' (cutoff red (ds @ [Left]) T\<^sub>1)) \<and>
             (\<not> a \<longrightarrow> internal p' (cutoff red (ds @ [Right]) T\<^sub>2))" 
          using b_p internal_inv_Branch[of p ?T\<^sub>1' ?T\<^sub>2'] by auto
        then have "\<not>red(ds @ [a] @ p')" using aa bb by (cases a) auto
        then show "\<not>red(ds @ p)" using b_p by simp
      qed
  }
  then show ?case by blast
qed

lemma cutoff_internal: "anybranch T red \<Longrightarrow> anyinternal (cutoff red [] T) (\<lambda>p. \<not>red p)" 
  using cutoff_internal'[of T red "[]"] by auto

lemma cutoff_branch_internal: 
  "anybranch T red \<Longrightarrow> \<exists>T'. anyinternal T' (\<lambda>p. \<not>red p) \<and> anybranch T' (\<lambda>p. red p)" 
  using cutoff_internal[of T] cutoff_branch[of T] by blast

section {* Possibly Infinite Trees *}
(* Possibly infinite trees are of type dir list set *)

abbreviation wf_tree :: "dir list set \<Rightarrow> bool" where
  "wf_tree T \<equiv> (\<forall>ds d. (ds @ d) \<in> T \<longrightarrow> ds \<in> T)"

(* The subtree in with root r *)
fun subtree :: "dir list set \<Rightarrow> dir list \<Rightarrow> dir list set" where 
  "subtree T r = {ds \<in> T. \<exists>ds'. ds = r @ ds'}" 

(* A subtree of a tree is either in the left branch, the right branch, or is the tree itself *)
lemma subtree_pos: 
  "subtree T ds \<subseteq> subtree T (ds @ [Left]) \<union> subtree T (ds @ [Right]) \<union> {ds}"
proof (rule subsetI; rule Set.UnCI)
  let ?subtree = "subtree T"
  fix x
  assume asm: "x \<in> ?subtree ds"
  assume "x \<notin> {ds}"
  then have "x \<noteq> ds" by simp
  then have "\<exists>e d. x = ds @ [d] @ e" using asm list.exhaust by auto
  then have "(\<exists>e. x = ds @ [Left] @ e) \<or> (\<exists>e. x = ds @ [Right] @ e)" using bool.exhaust by auto
  then show "x \<in> ?subtree (ds @ [Left]) \<union> ?subtree (ds @ [Right])" using asm by auto
qed

(* Infinite paths in trees should probably be nat \<Rightarrow> dir, instead of nat \<Rightarrow> dir list .   The nat \<Rightarrow> dir list are only useful locally.    I do the conversion in Resolution, I think, but I should rather do it here.    I am not 100% sure though. Perhaps this just means I must convert back to nat \<Rightarrow> dir list,    and that would be rather pointless. Perhaps, I could just do the conversion as a    corollary or something.*)
section {* Infinite Paths *}
(* aka list-chains *)
abbreviation list_chain :: "(nat \<Rightarrow> 'a list) \<Rightarrow> bool" where
  "list_chain f \<equiv> (f 0 = []) \<and> (\<forall>n. \<exists>a. f (Suc n) = (f n) @ [a])"

lemma chain_length: "list_chain f \<Longrightarrow> length (f n) = n"
apply (induction n)
apply auto
apply (metis length_append_singleton)
done

lemma chain_prefix: "list_chain f \<Longrightarrow> n\<^sub>1 \<le> n\<^sub>2 \<Longrightarrow> \<exists>a. (f n\<^sub>1) @ a = (f n\<^sub>2)"
proof (induction n\<^sub>2)
  case (Suc n\<^sub>2)
  then have "n\<^sub>1 \<le> n\<^sub>2 \<or> n\<^sub>1 = Suc n\<^sub>2" by auto
  then show ?case
    proof
      assume "n\<^sub>1 \<le> n\<^sub>2"
      then obtain a where a: "f n\<^sub>1 @ a = f n\<^sub>2" using Suc by auto
      have b: "\<exists>b. f (Suc n\<^sub>2) = f n\<^sub>2 @ [b]" using Suc by auto 
      from a b have "\<exists>b. f n\<^sub>1 @ (a @ [b]) = f (Suc n\<^sub>2)" by auto
      then show "\<exists>c. f n\<^sub>1 @ c = f (Suc n\<^sub>2)" by blast
    next
      assume "n\<^sub>1 = Suc n\<^sub>2"
      then have "f n\<^sub>1 @ [] = f (Suc n\<^sub>2)" by auto
      then show "\<exists>a. f n\<^sub>1 @ a = f (Suc n\<^sub>2)" by auto
    qed
qed auto

(* If we make a lookup in a list, then looking up in an extension gives us the same value *)
lemma ith_in_extension:
  assumes chain: "list_chain f"
  assumes smalli: "i < length (f n\<^sub>1)"
  assumes n\<^sub>1n\<^sub>2: "n\<^sub>1 \<le> n\<^sub>2"
  shows "f n\<^sub>1 ! i = f n\<^sub>2 ! i"
proof -
  from chain n\<^sub>1n\<^sub>2 have "\<exists>a. f n\<^sub>1 @ a = f n\<^sub>2" using chain_prefix by blast
  then obtain a where a_p: "f n\<^sub>1 @ a = f n\<^sub>2" by auto
  have "(f n\<^sub>1 @ a) ! i = f n\<^sub>1 ! i" using smalli by (simp add: nth_append) 
  then show ?thesis using a_p by auto
qed

section {* König's Lemma *}

lemma inf_subs: 
  assumes inf: "\<not>finite(subtree T ds)"
  shows "\<not>finite(subtree T (ds @ [Left])) \<or> \<not>finite(subtree T (ds @ [Right]))"
proof -
  let ?subtree = "subtree T"
  {
    assume asms: "finite(?subtree(ds @ [Left]))"
                 "finite(?subtree(ds @ [Right]))"
    have "?subtree ds \<subseteq> ?subtree (ds @ [Left] ) \<union> ?subtree (ds @ [Right]) \<union> {ds} " 
      using subtree_pos by auto
    then have "finite(?subtree (ds))" using asms by (simp add: finite_subset)
  } 
  then show "\<not>finite(?subtree (ds @ [Left])) \<or> \<not>finite(?subtree (ds @ [Right]))" using inf by auto
qed

fun buildchain :: "(dir list \<Rightarrow> dir list) \<Rightarrow> nat \<Rightarrow> dir list" where
  "buildchain next 0 = []"
| "buildchain next (Suc n) = next (buildchain next n)"

(* I have a function intree that checks if a path (node) is in the tree. Assume there are infinite such nodes.  Prove that I can make a chain of paths in the tree*)
lemma konig:
  assumes inf: "\<not>finite T"
  assumes wellformed: "wf_tree T"
  shows "\<exists>c. list_chain c \<and> (\<forall>n. (c n) \<in> T)"
proof
  let ?subtree = "subtree T"
  let ?nextnode = "\<lambda>ds. (if \<not>finite (subtree T (ds @ [Left])) then ds @ [Left] else ds @ [Right])"  (*?subtree instead of "subtree T" *)

  let ?c = "buildchain ?nextnode"

  have is_chain: "list_chain ?c" by auto

  from wellformed have prefix: "\<And>ds d. (ds @ d) \<in> T \<Longrightarrow> ds \<in> T" by blast

  { 
    fix n
    have "(?c n) \<in> T \<and> \<not>finite (?subtree (?c n))"
      proof (induction n)
        case 0
        have "\<exists>ds. ds \<in> T" using inf by (simp add: not_finite_existsD)
        then obtain ds where "ds \<in> T" by auto
        then have "([]@ds) \<in> T" by auto
        then have "[] \<in> T" using prefix[of "[]"] by auto 
        then show ?case using inf by auto
      next
        case (Suc n)
        from Suc have next_in:  "(?c n) \<in> T" by auto
        from Suc have next_inf: "\<not>finite (?subtree (?c n))" by auto

        from next_inf have next_next_inf:
           "\<not>finite (?subtree (?nextnode (?c n)))" 
              using inf_subs by auto
        then have "\<exists>ds. ds \<in> ?subtree (?nextnode (?c n))"
          by (simp add: not_finite_existsD)
        then obtain ds where dss: "ds \<in> ?subtree (?nextnode (?c n))" by auto
        then have "ds \<in> T" "\<exists>suf. ds = (?nextnode (?c n)) @ suf" by auto
        then obtain suf where "ds \<in> T \<and> ds = (?nextnode (?c n)) @ suf" by auto
        then have "(?nextnode (?c n)) \<in> T"
          using prefix[of "?nextnode (?c n)" suf] by auto
              
        then have "(?c (Suc n)) \<in> T" by auto
        then show ?case using next_next_inf by auto
      qed
  }
  then show "list_chain ?c \<and> (\<forall>n. (?c n)\<in> T) " using is_chain by auto
qed

end