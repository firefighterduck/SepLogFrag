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

theorem hypothesis: "P\<and>\<^sub>p\<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>' \<Longrightarrow> P\<and>\<^sub>p\<Pi>\<bar>\<Sigma> \<turnstile> P\<and>\<^sub>p\<Pi>'\<bar>\<Sigma>'"
unfolding entails_def by blast

theorem empty_ls: "\<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>' \<Longrightarrow> \<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>ls(E,E)*\<Sigma>'"
unfolding entails_def by fastforce

theorem nil_not_lval: "E\<^sub>1\<noteq>\<^sub>pnil \<and>\<^sub>p \<Pi>\<bar>E\<^sub>1\<longmapsto>E\<^sub>2 * \<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>' \<Longrightarrow> \<Pi>\<bar>E\<^sub>1\<longmapsto>E\<^sub>2 * \<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>'"
unfolding entails_def by force

theorem sep_conj_partial: "E\<^sub>1\<noteq>\<^sub>pE\<^sub>3 \<and>\<^sub>p \<Pi>\<bar>E\<^sub>1\<longmapsto>E\<^sub>2 * E\<^sub>3\<longmapsto>E\<^sub>4 * \<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>' 
  \<Longrightarrow> \<Pi>\<bar>E\<^sub>1\<longmapsto>E\<^sub>2 * E\<^sub>3\<longmapsto>E\<^sub>4 * \<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>'"
proof (rule entailment_lift)
  fix s h
  assume assm1: "E\<^sub>1\<noteq>\<^sub>pE\<^sub>3 \<and>\<^sub>p \<Pi>\<bar>E\<^sub>1\<longmapsto>E\<^sub>2 * E\<^sub>3\<longmapsto>E\<^sub>4 * \<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>'"
  assume assm2: "(s,h)\<Turnstile>\<Pi>\<bar>E\<^sub>1\<longmapsto>E\<^sub>2 * E\<^sub>3\<longmapsto>E\<^sub>4 * \<Sigma>"
  then obtain h1 h2 where "h=h1++h2" "h1\<bottom>h2" "(s,h1)\<Turnstile>Spat(E\<^sub>1\<longmapsto>E\<^sub>2)" "(s,h2)\<Turnstile>SpatF(E\<^sub>3\<longmapsto>E\<^sub>4 * \<Sigma>)"
    by fastforce
  moreover then obtain h3 h4 where "h2=h3++h4" "h3\<bottom>h4" "(s,h3)\<Turnstile>Spat(E\<^sub>3\<longmapsto>E\<^sub>4)" by auto
  ultimately have "\<lbrakk>E\<^sub>1\<rbrakk>s \<noteq> \<lbrakk>E\<^sub>3\<rbrakk>s" by fastforce
  hence "(s,h)\<Turnstile>Pure(E\<^sub>1\<noteq>\<^sub>pE\<^sub>3)" by auto
  with assm2 have "(s,h)\<Turnstile>E\<^sub>1\<noteq>\<^sub>pE\<^sub>3 \<and>\<^sub>p \<Pi>\<bar>E\<^sub>1\<longmapsto>E\<^sub>2 * E\<^sub>3\<longmapsto>E\<^sub>4 * \<Sigma>" by auto
  with assm1 show "(s,h)\<Turnstile>\<Pi>'\<bar>\<Sigma>'" by (simp add: entails_def)
qed

theorem frame: "\<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>' \<Longrightarrow> \<Pi>\<bar>S * \<Sigma> \<turnstile> \<Pi>'\<bar>S * \<Sigma>'"
proof (rule entailment_lift)
  fix s h
  assume assm1: "\<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>'"
  assume assm2: "(s,h)\<Turnstile>\<Pi>\<bar>S * \<Sigma>"
  then obtain h1 h2 where sep_conj: "h=h1++h2" "h1\<bottom>h2" "(s,h1)\<Turnstile>Spat S" "(s,h2)\<Turnstile>SpatF \<Sigma>" by fast
  moreover {
    from assm2 have "(s,h)\<Turnstile>PureF \<Pi>" by fastforce
    from heap_puref[OF this] have "(s,h2)\<Turnstile>PureF \<Pi>" by simp
    with sep_conj(4) have "(s,h2)\<Turnstile>\<Pi>\<bar>\<Sigma>" by fast
    with assm1 have "(s,h2)\<Turnstile>\<Pi>'\<bar>\<Sigma>'" by (simp add: entails_def)
    hence "(s,h2)\<Turnstile>PureF \<Pi>'" "(s,h2)\<Turnstile>SpatF \<Sigma>'" by auto
  }
  ultimately show "(s,h)\<Turnstile>\<Pi>'\<bar>S * \<Sigma>'" using heap_puref by blast
qed
end