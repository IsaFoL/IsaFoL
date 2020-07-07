theory IsaSAT_EMA
  imports IsaSAT_Literals
begin

section \<open>Moving averages\<close>

text \<open>We use (at least hopefully) the variant of EMA-14 implemented in Cadical, but with fixed-point
calculation (\<^term>\<open>1 :: nat\<close> is \<^term>\<open>(1 :: nat) >> 32\<close>).

Remark that the coefficient \<^term>\<open>\<beta>\<close> already should not take care of the fixed-point conversion of the glue.
Otherwise, \<^term>\<open>value\<close> is wrongly updated.
\<close>
type_synonym ema = \<open>64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word\<close>

definition ema_bitshifting where
  \<open>ema_bitshifting = (1 << 32)\<close>


definition (in -) ema_update :: \<open>nat \<Rightarrow> ema \<Rightarrow> ema\<close> where
  \<open>ema_update = (\<lambda>lbd (value, \<alpha>, \<beta>, wait, period).
     let lbd = (of_nat lbd) * ema_bitshifting in
     let value = if lbd > value then value + (\<beta> * (lbd - value) >> 32) else value - (\<beta> * (value - lbd) >> 32) in
     if \<beta> \<le> \<alpha> \<or> wait > 0 then (value, \<alpha>, \<beta>, wait - 1, period)
     else
       let wait = 2 * period + 1 in
       let period = wait in
       let \<beta> = \<beta> >> 1 in
       let \<beta> = if \<beta> \<le> \<alpha> then \<alpha> else \<beta> in
       (value, \<alpha>, \<beta>, wait, period))\<close>

definition (in -) ema_init :: \<open>64 word \<Rightarrow> ema\<close> where
  \<open>ema_init \<alpha> = (0, \<alpha>, ema_bitshifting, 0, 0)\<close>

fun ema_reinit where
  \<open>ema_reinit (value, \<alpha>, \<beta>, wait, period) = (value, \<alpha>, 1 << 32, 0, 0)\<close>

fun ema_get_value :: \<open>ema \<Rightarrow> 64 word\<close> where
  \<open>ema_get_value (v, _) = v\<close>

fun ema_extract_value :: \<open>ema \<Rightarrow> 64 word\<close> where
  \<open>ema_extract_value (v, _) = v >> 32\<close>


text \<open>We use the default values for Cadical: \<^term>\<open>(3 / 10 ^2)\<close> and  \<^term>\<open>(1 / 10 ^ 5)\<close>  in our fixed-point
  version.
\<close>

abbreviation ema_fast_init :: ema where
  \<open>ema_fast_init \<equiv> ema_init (128849010)\<close>

abbreviation ema_slow_init :: ema where
  \<open>ema_slow_init \<equiv> ema_init 429450\<close>


end