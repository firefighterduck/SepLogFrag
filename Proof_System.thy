theory Proof_System
imports Entailment
begin

section \<open>Rules of the proof System\<close>
text \<open>The proof system at the core of the decision procedure is based on the following rules.\<close>

theorem axiom: "\<Pi>\<bar>emp \<turnstile> \<top>\<bar>emp"
by (auto simp: entails_def)

theorem inconsistent: "E\<noteq>\<^sub>pE \<and>\<^sub>p \<Pi>\<bar>\<Sigma> \<turnstile> F"
by (auto simp: entails_def)

theorem substitution: "subst x E (\<Pi>\<bar>\<Sigma>) \<turnstile> subst x E (\<Pi>'\<bar>\<Sigma>') \<Longrightarrow> \<acute>x`=\<^sub>pE \<and>\<^sub>p \<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>'"
proof (rule entailment_lift)
  fix s h
  assume assm1: "subst x E (\<Pi>\<bar>\<Sigma>) \<turnstile> subst x E (\<Pi>'\<bar>\<Sigma>')"
  assume assm2: "(s,h)\<Turnstile>\<acute>x`=\<^sub>pE\<and>\<^sub>p\<Pi>\<bar>\<Sigma>"
  hence s_eq: "\<lbrakk>\<acute>x`\<rbrakk>s=\<lbrakk>E\<rbrakk>s" and "(s,h)\<Turnstile>\<Pi>\<bar>\<Sigma>" by fast+
  hence "(s,h)\<Turnstile>subst x E (\<Pi>\<bar>\<Sigma>)" using subst_sat_rev by blast
  with assm1 have "(s,h)\<Turnstile>subst x E (\<Pi>'\<bar>\<Sigma>')" by (simp add: entails_def)
  with s_eq show "(s,h)\<Turnstile>\<Pi>'\<bar>\<Sigma>'" using subst_sat by blast
qed

theorem eq_reflexivel: "\<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>' \<Longrightarrow> E=\<^sub>pE\<and>\<^sub>p\<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>'"
unfolding entails_def by blast

theorem eq_reflexiver: "\<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>' \<Longrightarrow> \<Pi>\<bar>\<Sigma> \<turnstile> E=\<^sub>pE\<and>\<^sub>p\<Pi>'\<bar>\<Sigma>'"
unfolding entails_def by blast
end