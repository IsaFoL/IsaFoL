(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2017)
Author:  Guillaume Allais (2011)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2014,2017)
Author:  Martin Avanzini <martin.avanzini@uibk.ac.at> (2014)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
Author:  Sarah Winkler <sarah.winkler@uibk.ac.at> (2014)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)

chapter \<open>First-Order Terms\<close>

theory CeTA_Term_More
imports
  Knuth_Bendix_Order.Subterm_and_Context
  First_Order_Terms.Term
begin

lemma size_subst: "size t \<le> size (t \<cdot> \<sigma>)"
proof (induct t)
  case (Var x)
  then show ?case by (cases "\<sigma> x") auto
next
  case (Fun f ss)
  then show ?case
    by (simp add: o_def, induct ss, force+)
qed

lemma size_ctxt: "size t \<le> size (C\<langle>t\<rangle>)"
by (induct C) simp_all

lemma size_ne_ctxt: "C \<noteq> \<box> \<Longrightarrow> size t < size (C\<langle>t\<rangle>)"
by (induct C) force+

lemma eq_ctxt_subst_iff [simp]:
  "(t = C\<langle>t \<cdot> \<sigma>\<rangle>) \<longleftrightarrow> C = \<box> \<and> (\<forall>x\<in>vars_term t. \<sigma> x = Var x)" (is "?L = ?R")
proof
  assume t: "?L"
  then have "size t = size (C\<langle>t \<cdot> \<sigma>\<rangle>)" by simp
  with size_ne_ctxt [of C "t \<cdot> \<sigma>"] and size_subst [of t \<sigma>]
    have [simp]: "C = \<box>" by auto
  have "\<forall>x\<in>vars_term t. \<sigma> x = Var x" using t and term_subst_eq_conv [of t Var] by simp
  then show ?R by auto
next
  assume ?R
  then show ?L using term_subst_eq_conv [of t Var] by simp
qed

lemma ctxt_subst_id[simp]: "C \<cdot>\<^sub>c Var = C" by (induct C, auto)

end