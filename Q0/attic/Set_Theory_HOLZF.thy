theory Set_Theory_HOLZF imports "../Set_Theory" begin

(* We prove that our specification lives up to the axioms in MainZF.
   The axioms are copied here.
 *)

context set_theory begin

definition Elem where 
  "Elem \<equiv> mem"

definition Empty where
  "Empty \<equiv> Ø"

definition Sum where 
  "Sum \<equiv> uni"

definition Power where 
  "Power \<equiv> pow"

definition subset where 
  "subset \<equiv> subs"

abbreviation Upair where
  "Upair \<equiv> upair"

definition Singleton:: "'s \<Rightarrow> 's" where
  "Singleton x == Upair x x"

definition union :: "'s \<Rightarrow> 's \<Rightarrow> 's" where
  "union A B == Sum (Upair A B)"

definition SucNat:: "'s \<Rightarrow> 's" where
  "SucNat x == union x (Singleton x)"

lemma Empty: "\<not> (Elem x Empty)"
  unfolding Elem_def Empty_def using mem_empty .

lemma Ext: "(x = y) = (\<forall>z. Elem z x = Elem z y)" 
  unfolding Elem_def using extensional .

lemma Sum: "Elem z (Sum x) = (\<exists>y. Elem z y \<and> Elem y x)"
  unfolding Sum_def Elem_def using mem_uni .

lemma Power: "Elem y (Power x) = (subset y x)"
  unfolding Elem_def Power_def subset_def subs_def ..

definition Repl :: "'s \<Rightarrow> ('s \<Rightarrow> 's) \<Rightarrow> 's" where
  "Repl \<equiv> undefined"

(* I have to define Repl *)
lemma Repl: "Elem b (Repl A f) = (\<exists>a. Elem a A \<and> b = f a)"
  sorry

lemma Regularity: "A \<noteq> Empty \<longrightarrow> (\<exists>x. Elem x A \<and> (\<forall>y. Elem y x \<longrightarrow> \<not> (Elem y A)))"
  apply auto
  sorry

(* I have to define Infi and SucNat *)
lemma Infinity: "Elem Empty Infi \<and> (\<forall>x. Elem x Infi \<longrightarrow> Elem (SucNat x) Infi)"
  sorry

end

  

end