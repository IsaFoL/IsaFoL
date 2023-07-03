theory IsaSAT_EMA
  imports IsaSAT_Literals
begin

section \<open>Moving averages\<close>

definition EMA_FIXPOINT_SIZE :: \<open>nat\<close> where
  \<open>EMA_FIXPOINT_SIZE = 32\<close>

text \<open>We use (at least hopefully) the variant of EMA-14 implemented in Cadical, but with fixed-point
calculations (\<^term>\<open>1 :: nat\<close> is \<^term>\<open>(1 :: nat) >> EMA_FIXPOINT_SIZE\<close>).

Remark that the coefficient \<^term>\<open>\<beta>\<close> already should take care of the fixed-point conversion of the glue.
Otherwise, \<^term>\<open>value\<close> is wrongly updated.
\<close>
type_synonym ema = \<open>64 word \<times> 64 word \<times> 64 word \<times> 64 word \<times> 64 word\<close>

definition ema_bitshifting where
  \<open>ema_bitshifting = (1 << EMA_FIXPOINT_SIZE)\<close>


definition EMA_MULT_SHIFT :: \<open>nat\<close> where
  \<open>EMA_MULT_SHIFT = 8\<close>

text \<open>TODO: some precision is lost  here in the difference calculation.\<close>
definition (in -) ema_update :: \<open>nat \<Rightarrow> ema \<Rightarrow> ema\<close> where
  \<open>ema_update = (\<lambda>lbd (value, \<alpha>, \<beta>, wait, period).
     let lbd = (of_nat lbd) * ema_bitshifting in
     let value = if lbd > value
        then value + ((\<beta> >> (EMA_FIXPOINT_SIZE - EMA_MULT_SHIFT)) * ((lbd - value) >> EMA_MULT_SHIFT))
        else value - ((\<beta> >> (EMA_FIXPOINT_SIZE - EMA_MULT_SHIFT)) * ((value - lbd) >> EMA_MULT_SHIFT))
     in
     let wait = wait - 1 in
       if \<beta> \<le> \<alpha> \<or> wait > 0 then (value, \<alpha>, \<beta>, wait, period)
     else
       let wait = 2 * (period+1)-1 in
       let period = wait in
       let \<beta> = \<beta> >> 1 in
       let \<beta> = if \<beta> \<le> \<alpha> then \<alpha> else \<beta> in
       (value, \<alpha>, \<beta>, wait, period))\<close>

definition (in -) ema_init :: \<open>64 word \<Rightarrow> ema\<close> where
  \<open>ema_init \<alpha> = (0, \<alpha>  >> (EMA_FIXPOINT_SIZE - 32), ema_bitshifting, 0, 0)\<close>

fun ema_reinit where
  \<open>ema_reinit (value, \<alpha>, \<beta>, wait, period) = (value, \<alpha>, ema_bitshifting, 0, 0)\<close>

fun ema_get_value :: \<open>ema \<Rightarrow> 64 word\<close> where
  \<open>ema_get_value (v, _) = v\<close>

fun ema_extract_value :: \<open>ema \<Rightarrow> 64 word\<close> where
  \<open>ema_extract_value (v, _) = v >> EMA_FIXPOINT_SIZE\<close>


text \<open>We use the default values for Cadical: \<^term>\<open>(3 / 10 ^2)\<close> and  \<^term>\<open>(1 / 10 ^ 5)\<close>  in our fixed-point
  version.
\<close>
value \<open>((3 :: 64 word) << EMA_FIXPOINT_SIZE) >> (15)\<close>
value \<open>((4 :: 64 word) << EMA_FIXPOINT_SIZE >> 7)\<close>
abbreviation ema_fast_init :: ema where
  \<open>ema_fast_init \<equiv> ema_init (128849010)\<close> \<comment> \<open>5629499534213\<close>

abbreviation ema_slow_init :: ema where
  \<open>ema_slow_init \<equiv> ema_init (429450)\<close> \<comment> \<open>2814749767\<close>

text \<open>Small test below. It was useful once to detect an overflow that lead to very bad
  initialisation behaviour.\<close>

value \<open>let \<alpha> = shiftr 128849010 (EMA_FIXPOINT_SIZE - 32);
        x =  (((ema_update 10)^^ 1) (7 * ema_bitshifting, \<alpha>, \<alpha>, 12, 12))
  in (ema_extract_value x, ema_get_value x, x)\<close>

end
