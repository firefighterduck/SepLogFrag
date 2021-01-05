theory Examples
imports "../Sep_Log_Frag"
begin 

section \<open>Examples\<close>
text \<open>In this section, some example entailments are either proven or disproven by usage of
      the decision procedures rules.\<close>

subsection \<open>Auxiliary lemmata:\<close>
lemma spatial_commut_entail: "\<Pi>\<bar>(s1*s2*\<Sigma>) \<turnstile> consequent \<Longrightarrow> \<Pi>\<bar>(s2*s1*\<Sigma>) \<turnstile> consequent"
using entails_def spatial_commut_form by force
lemma pure_commut_entail: "(p1\<and>\<^sub>pp2\<and>\<^sub>p\<Pi>)\<bar>\<Sigma> \<turnstile> consequent \<Longrightarrow> (p2\<and>\<^sub>pp1\<and>\<^sub>p\<Pi>)\<bar>\<Sigma> \<turnstile> consequent"
using entails_def pure_commut_form by simp

subsection \<open>First example (cf. \cite{seminar-paper} 2.4)\<close>
lemma "[\<acute>x`\<noteq>\<^sub>p\<acute>p`]\<bar>\<acute>x`\<longmapsto>\<acute>y` * \<acute>y`\<longmapsto>nil * emp \<turnstile> []\<bar>[ls(\<acute>x`,nil)]"
\<comment> \<open>First enrichen the formula to contain all necessary inequalities, ...\<close>
apply (rule nil_not_lval)
apply (rule spatial_commut_entail)  (* Reordering *)
apply (rule nil_not_lval)
\<comment> \<open>... then destructure the ls step by step, ...\<close>
apply (rule pure_commut_entail)     (* Reordering *)
apply (rule spatial_commut_entail)  (* Reordering *)
apply (rule non_empty_ls)
apply (rule pure_commut_entail)     (* Reordering *)
apply (rule non_empty_ls)
\<comment> \<open>... then exchange the empty ls with emp ...\<close>
apply (rule empty_ls)
\<comment> \<open>... and finally prove the entailment with the axiom. \<close>
by (rule axiom)
end