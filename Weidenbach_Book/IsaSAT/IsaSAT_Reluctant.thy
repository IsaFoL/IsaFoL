theory IsaSAT_Reluctant
  imports More_Sepref.WB_More_Refinement
    Isabelle_LLVM.Bits_Natural (*Watched_Literals.WB_Word*)
begin

text \<open>
  In this file, we define the Luby sequence, based on the implementation from CaDiCaL.
\<close>

datatype reluctant =
  Reluctant
    (reluctant_limited: bool)
    (reluctant_trigger: bool)
    (reluctant_u: \<open>64 word\<close>)
    (reluctant_v: \<open>64 word\<close>)
    (reluctant_period: \<open>64 word\<close>)
    (reluctant_wait: \<open>64 word\<close>)
    (reluctant_limit: \<open>64 word\<close>)

definition reluctant_set_trigger :: \<open>bool \<Rightarrow> reluctant \<Rightarrow> reluctant\<close> where
  \<open>reluctant_set_trigger trigger r =
     (let
    limited = reluctant_limited r;
    u = reluctant_u r;
    v = reluctant_v r;
    period = reluctant_period r;
    wait = reluctant_wait r;
    limit = reluctant_limit r in Reluctant limited trigger u v period wait limit)\<close>

definition reluctant_disable :: \<open>reluctant \<Rightarrow> reluctant\<close> where
  \<open>reluctant_disable r =
  (let
    limited = reluctant_limited r;
    trigger = reluctant_trigger r;
    u = reluctant_u r;
    v = reluctant_v r;
    period = reluctant_period r;
    wait = reluctant_wait r;
  limit = reluctant_limit r in
  (Reluctant limited trigger u v 0 wait limit))\<close>

definition reluctant_untrigger :: \<open>reluctant \<Rightarrow> reluctant\<close> where
  \<open>reluctant_untrigger r = (reluctant_set_trigger False r)\<close>

definition reluctant_triggered :: \<open>reluctant \<Rightarrow> reluctant \<times> bool\<close> where
  \<open>reluctant_triggered r = (reluctant_set_trigger False r, reluctant_trigger r)\<close>

definition reluctant_triggered2 :: \<open>reluctant \<Rightarrow> bool\<close> where
  \<open>reluctant_triggered2 r = (reluctant_trigger r)\<close>

definition reluctant_tick :: \<open>reluctant \<Rightarrow> reluctant\<close> where
  \<open>reluctant_tick  r =
  (let
    limited = reluctant_limited r;
    trigger = reluctant_trigger r;
    u = reluctant_u r;
    v = reluctant_v r;
    period = reluctant_period r;
    wait = reluctant_wait r;
    limit = reluctant_limit r in
  (if period = 0 \<or> trigger then Reluctant limited trigger u v period (wait) limit
   else if wait > 1 then Reluctant limited trigger u v period (wait - 1) limit
   else let (u, v) = (if u AND (0-u) = v then (u+1, 1) else (u, 2 * v));
      (u, v) = (if limited \<and> wait > limit then (1,1) else (u, v));
      wait = v * period in
    Reluctant limited True u v period wait limit))\<close>

definition reluctant_enable :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> reluctant\<close> where
  \<open>reluctant_enable period limit =
  (let limited = limit \<noteq> 0;
       period = (if limited \<and> period > limit then limit else period)
     in
    Reluctant limited False 1 1 period period limit)\<close>

definition reluctant_init :: \<open>reluctant\<close> where
  \<open>reluctant_init = reluctant_enable (1<< 10) (1<<20)\<close>


value
  \<open>let p0 = (reluctant_tick ^^ 1024) (reluctant_enable (1<< 10) (1<<20));
    p1 = reluctant_untrigger p0;
    p2 = (reluctant_tick ^^ 1024) p1;
    p3 = reluctant_untrigger p2;
    p4 = (reluctant_tick ^^ 2048) p3;
    p5 = reluctant_untrigger p3;
    p6 = (reluctant_tick ^^ 2048) p5 in
   (p0, p1, p2, p3, p4, p5, p6, reluctant_triggered2 p0 = True, reluctant_triggered2 p2 = False)\<close>
end