section {* More Terms and Literals *}

theory ExtraSnippets imports Main begin

(* Adapted from Nipkow and Klein's Concrete semantics *)  
  
text_raw {*\DefineSnippet{cantor}{*}
theorem cantor: "\<not> surj(f :: 'a \<Rightarrow> 'a set)"
proof
  assume "surj f"
  then have "\<forall>A. \<exists>a. A = f a" using surj_def by metis
  then have "\<exists>a. {x. x \<notin> f x} = f a" by blast
  then obtain a where "{x. x \<notin> f x} = f a" by blast
  then show "False" by blast
qed
text_raw {*}%EndSnippet*}
  
text_raw {*\DefineSnippet{idexample}{*}
lemma identities:
  assumes "\<forall>y. identity y = y"
  shows "identity (identity (identity x)) = x"
proof -
  have "identity (identity (identity x)) = identity (identity x)" using assms by auto
  also have "... = identity x" using assms by auto
  also have "... = x" using assms by auto
  finally show "identity (identity (identity x)) = x" by -
qed
text_raw {*}%EndSnippet*}

end

