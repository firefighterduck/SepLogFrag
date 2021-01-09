theory Model_Theory
imports "../basic_theory/Entailment" Proof_System
begin

section \<open>Decidability, Model-Theoretical\<close>
text \<open>This section contains proofs from the corresponding section 3 in \cite{JoshBerdine.2004} about
      decidability, soundness and completeness.\<close>

text \<open>Entailments without ls in the antecedent are decidable, cf. Lemma 3 \cite{JoshBerdine.2004}.\<close>
theorem entailment_decidable_simple: "\<And>\<Pi> \<Sigma> \<Pi>' \<Sigma>'. \<nexists>E\<^sub>1 E\<^sub>2. ls(E\<^sub>1,E\<^sub>2) \<in> set \<Sigma> 
  \<Longrightarrow> \<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>' \<or> \<not>(\<Pi>\<bar>\<Sigma> \<turnstile> \<Pi>'\<bar>\<Sigma>')"
  unfolding entails_def by blast 
(* I'm pretty sure that this is not how decidability would actually be formalized, yet I lack ideas
   of how this would be possible otherwise. I suppose pretty much every predicate defined in Isabelle
   is in fact decidable as it would otherwise not be accepted by the system.*)

subsection \<open>Proof of the above theorem as in \cite{JoshBerdine.2004}, A.2.\<close>
definition state_equiv :: "state \<Rightarrow> var set \<Rightarrow> state \<Rightarrow> bool" where 
  "state_equiv sh X sh' \<equiv> \<exists>s h s' h'. sh = (s,h) \<and> sh' = (s',h') \<and> (\<exists>r. bij r \<and> r Nilval = Nilval 
    \<and> (\<forall>x \<in> X. r (s x) = s' x) \<and> (\<forall>l l'. (l \<notin> dom h \<and> r (Val l) = Val l' \<and> l' \<notin> dom h') 
      \<or> ((r (Val l))) = Val l' \<and> r (the (h l)) = the (h' l')))"
notation state_equiv ("_ \<approx>\<^sub>_ _" [60,61,61] 61)

text \<open>cf Lemma 19 in \cite{JoshBerdine.2004}, A.2\<close>
(* This lemma seems to be rather simple to prove yet very tedious.
   Therefore (and because I'm writing this on 2021-01-09), I will not finish it. *)
lemma "\<lbrakk>X=fv A; (s,h)\<approx>\<^sub>X(s',h')\<rbrakk> \<Longrightarrow> ((s,h)\<Turnstile>A) = ((s',h')\<Turnstile>A)"
proof 
  assume X: "X=fv A"
  assume equiv: "(s,h)\<approx>\<^sub>X(s',h')"
  assume lhs: "(s,h)\<Turnstile>A"
  from lhs equiv X show "(s',h')\<Turnstile>A" proof (induction rule: sat_induct)
    case (EqSat e1 s e2 h)
    then obtain r where r: "(bij r \<and> r Nilval = Nilval 
      \<and> (\<forall>x \<in> X. r (s x) = s' x) \<and> (\<forall>l l'. (l \<notin> dom h \<and> r (Val l) = Val l' \<and> l' \<notin> dom h') 
        \<or> ((r (Val l))) = Val l' \<and> r (the (h l)) = the (h' l')))" using state_equiv_def by auto    
    with EqSat.prems(2) have r_eq: "\<forall>x \<in> fv e1 \<union> fv e2. r (s x) = s' x" by simp
    show ?case proof (cases e1)
      case Nil
      hence e1_nil: "\<lbrakk>e1\<rbrakk>s' = Nilval" by simp
      from Nil have s_e1_nil: "\<lbrakk>e1\<rbrakk>s = Nilval" by simp
      then show ?thesis proof (cases e2)
        case Nil
        hence "\<lbrakk>e2\<rbrakk>s' = Nilval" by simp
        with e1_nil show ?thesis by fastforce
      next
        case (Var x2)
        with s_e1_nil EqSat.hyps have "s x2 = Nilval" by simp
        moreover with r_eq have "r (s x2) = s' x2" by (simp add: Var)
        ultimately have "\<lbrakk>e2\<rbrakk>s' = Nilval" using r Var by simp
        with e1_nil show ?thesis by fastforce
      qed
    next
      case (Var a)
      with r_eq have "r (s a) = s' a" by simp
      hence e1_eq: "\<lbrakk>e1\<rbrakk>s' = r (\<lbrakk>e1\<rbrakk>s)" using Var by simp
      then show ?thesis proof (cases e2)
        case Nil
        hence "\<lbrakk>e2\<rbrakk>s = Nilval" by simp
        with EqSat.hyps have "\<lbrakk>e1\<rbrakk>s = Nilval" by simp
        with e1_eq r have "\<lbrakk>e1\<rbrakk>s' = Nilval" by simp
        moreover from Nil have "\<lbrakk>e2\<rbrakk>s' = Nilval" by fastforce
        ultimately show ?thesis by fastforce
      next
        case (Var b)
        with r_eq have "r (s b) = s' b" by simp
        hence "\<lbrakk>e2\<rbrakk>s' = r (\<lbrakk>e2\<rbrakk>s)" using Var by simp
        with e1_eq EqSat.hyps show ?thesis by auto
      qed
    qed
  next
    case (NeqSat e1 s e2 h)
    then show ?case sorry
  next
    case (TrueSat s h)
    then show ?case sorry
  next
    case (ConjSat s h P \<Pi>)
    then show ?case sorry
  next
    case (PointsToSat e1 s v h e2)
    then show ?case sorry
  next
    case (EmpSat h s)
    then show ?case sorry
  next
    case (SepConjSat h1 h2 h s S \<Sigma>)
    then show ?case sorry
  next
    case (FormSat s h \<Pi> \<Sigma>)
    then show ?case sorry
  next
    case (LsSat s h n e1 e2)
    then show ?case sorry
  qed
next
  assume X: "X=fv A"
  assume equiv: "(s,h)\<approx>\<^sub>X(s',h')"
  assume rhs: "(s',h')\<Turnstile>A"
  show "(s,h)\<Turnstile>A" \<comment> \<open>Works pretty much the same as above, but one has to reverse r.\<close>
  sorry
qed
end