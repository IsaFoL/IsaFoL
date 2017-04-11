theory Bits_Natural
imports IICF
  "~~/src/HOL/Word/Bits_Bit"
  "~~/src/HOL/Word/Bool_List_Representation"
begin

instantiation nat :: bits
begin

definition test_bit_nat :: \<open>nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  "test_bit i j = test_bit (int i) j"

definition lsb_nat :: \<open>nat \<Rightarrow> bool\<close> where
  "lsb i = (int i :: int) !! 0"

definition set_bit_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> nat" where
  "set_bit i n b = nat (bin_sc n b (int i))"

definition set_bits_nat :: "(nat \<Rightarrow> bool) \<Rightarrow> nat" where
  "set_bits f =
  (if \<exists>n. \<forall>n'\<ge>n. \<not> f n' then
     let n = LEAST n. \<forall>n'\<ge>n. \<not> f n'
     in nat (bl_to_bin (rev (map f [0..<n])))
   else if \<exists>n. \<forall>n'\<ge>n. f n' then
     let n = LEAST n. \<forall>n'\<ge>n. f n'
     in nat (sbintrunc n (bl_to_bin (True # rev (map f [0..<n]))))
   else 0 :: nat)"

definition shiftl_nat where
  "shiftl x n = nat ((int x) * 2 ^ n)"

definition shiftr_nat where
  "shiftr x n = nat (int x div 2 ^ n)"

definition bitNOT_nat :: "nat \<Rightarrow> nat" where
  "bitNOT i = nat (bitNOT (int i))"

definition bitAND_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bitAND i j = nat (bitAND (int i) (int j))"

definition bitOR_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bitOR i j = nat (bitOR (int i) (int j))"

definition bitXOR_nat :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "bitXOR i j = nat (bitXOR (int i) (int j))"

instance ..

end


lemma nat_shiftr[simp]:
  "m >> 0 = m"
  \<open>((0::nat) >> m) = 0\<close>
  \<open>(m >> Suc n) = (m div 2 >> n)\<close> for m :: nat
  by (auto simp: shiftr_nat_def zdiv_int zdiv_zmult2_eq[symmetric])

lemma nat_shifl_div: \<open>m >> n = m div (2^n)\<close> for m :: nat
  by (induction n arbitrary: m) (auto simp: div_mult2_eq)

lemma nat_shiftl[simp]:
  "m << 0 = m"
  \<open>((0::nat) << m) = 0\<close>
  \<open>(m << Suc n) = ((m * 2) << n)\<close> for m :: nat
  by (auto simp: shiftl_nat_def zdiv_int zdiv_zmult2_eq[symmetric])

lemma nat_shiftr_div2: \<open>m >> 1 = m div 2\<close> for m :: nat
  by auto

lemma nat_shiftr_div: \<open>m << n = m * (2^n)\<close> for m :: nat
  by (induction n arbitrary: m) (auto simp: div_mult2_eq)

definition shiftl1 :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>shiftl1 n = n << 1\<close>

definition shiftr1 :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>shiftr1 n = n >> 1\<close>

instantiation natural :: bits
begin

context includes natural.lifting begin

lift_definition test_bit_natural :: \<open>natural \<Rightarrow> nat \<Rightarrow> bool\<close> is test_bit .

lift_definition lsb_natural :: \<open>natural \<Rightarrow> bool\<close> is lsb .

lift_definition set_bit_natural :: "natural \<Rightarrow> nat \<Rightarrow> bool \<Rightarrow> natural" is
  set_bit .

lift_definition set_bits_natural :: \<open>(nat \<Rightarrow> bool) \<Rightarrow> natural\<close>
  is \<open>set_bits :: (nat \<Rightarrow> bool) \<Rightarrow> nat\<close> .

lift_definition shiftl_natural :: \<open>natural \<Rightarrow> nat \<Rightarrow> natural\<close>
  is \<open>shiftl :: nat \<Rightarrow> nat \<Rightarrow> nat\<close> .

lift_definition shiftr_natural :: \<open>natural \<Rightarrow> nat \<Rightarrow> natural\<close>
  is \<open>shiftr :: nat \<Rightarrow> nat \<Rightarrow> nat\<close> .

lift_definition bitNOT_natural :: \<open>natural \<Rightarrow> natural\<close>
  is \<open>bitNOT :: nat \<Rightarrow> nat\<close> .

lift_definition bitAND_natural :: \<open>natural \<Rightarrow> natural \<Rightarrow> natural\<close>
  is \<open>bitAND :: nat \<Rightarrow> nat \<Rightarrow> nat\<close> .

lift_definition bitOR_natural :: \<open>natural \<Rightarrow> natural \<Rightarrow> natural\<close>
  is \<open>bitOR :: nat \<Rightarrow> nat \<Rightarrow> nat\<close> .

lift_definition bitXOR_natural :: \<open>natural \<Rightarrow> natural \<Rightarrow> natural\<close>
  is \<open>bitXOR :: nat \<Rightarrow> nat \<Rightarrow> nat\<close> .

end

instance ..
end

context includes natural.lifting begin
lemma [code]:
  "integer_of_natural (m >> n) = (integer_of_natural m) >> n"
  apply transfer
  by (smt integer_of_natural.rep_eq msb_int_def msb_shiftr nat_eq_iff2 negative_zle
      shiftr_int_code shiftr_int_def shiftr_nat_def shiftr_natural.rep_eq
      type_definition.Rep_inject type_definition_integer)

lemma [code]:
  "integer_of_natural (m << n) = (integer_of_natural m) << n"
  apply transfer
  by (smt integer_of_natural.rep_eq msb_int_def msb_shiftl nat_eq_iff2 negative_zle
      shiftl_int_code shiftl_int_def shiftl_nat_def shiftl_natural.rep_eq
      type_definition.Rep_inject type_definition_integer)

end


lemma bitXOR_1_if_mod_2: \<open>bitXOR L 1 = (if L mod 2 = 0 then L + 1 else L - 1)\<close> for L :: nat
  apply transfer
  apply (subst int_int_eq[symmetric])
  apply (rule bin_rl_eqI)
   apply (auto simp: bitXOR_nat_def)
  unfolding bin_rest_def bin_last_def bitXOR_nat_def
       apply presburger+
  done

lemma bitAND_1_mod_2: \<open>bitAND L 1 = L mod 2\<close> for L :: nat
  apply transfer
  apply (subst int_int_eq[symmetric])
  apply (subst bitAND_nat_def)
   by (auto simp: zmod_int bin_rest_def bin_last_def bitval_bin_last[symmetric])

end