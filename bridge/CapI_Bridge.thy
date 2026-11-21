theory CapI_Bridge
  imports LambdaCapEnvWeakHead.Uniform LambdaCapEnv.Reduction
begin

section \<open>Connection to the calculus of \<^verbatim>\<open>lambda-capenv-public\<close> (capI)\<close>

text \<open>
  The term syntax of this development is in bijection with capI's
  (\<open>Var, Lam, App, Comp, Nil, Extn\<close> correspond to \<open>V, Lam, App, Cmp, Emp, Ext\<close>), and
  \<open>\<sigma>\<close> together with \<open>\<beta>\<close> under all congruences is exactly capI's one-step reduction
  \<open>red\<close>.  In particular weak-head reduction is a sub-relation of \<open>red\<close>.
\<close>

fun toI :: "Cap_Syntax.trm \<Rightarrow> Syntax.trm" where
  "toI (Cap_Syntax.trm.Var x) = Syntax.trm.V x"
| "toI (Cap_Syntax.trm.Lam x M) = Syntax.trm.Lam x (toI M)"
| "toI (Cap_Syntax.trm.App M N) = Syntax.trm.App (toI M) (toI N)"
| "toI Cap_Syntax.trm.Nil = Syntax.trm.Emp"
| "toI (Cap_Syntax.trm.Extn M x N) = Syntax.trm.Ext (toI M) x (toI N)"
| "toI (Cap_Syntax.trm.Comp M N) = Syntax.trm.Cmp (toI M) (toI N)"

fun ofI :: "Syntax.trm \<Rightarrow> Cap_Syntax.trm" where
  "ofI (Syntax.trm.V x) = Cap_Syntax.trm.Var x"
| "ofI (Syntax.trm.Lam x M) = Cap_Syntax.trm.Lam x (ofI M)"
| "ofI (Syntax.trm.App M N) = Cap_Syntax.trm.App (ofI M) (ofI N)"
| "ofI Syntax.trm.Emp = Cap_Syntax.trm.Nil"
| "ofI (Syntax.trm.Ext M x N) = Cap_Syntax.trm.Extn (ofI M) x (ofI N)"
| "ofI (Syntax.trm.Cmp M N) = Cap_Syntax.trm.Comp (ofI M) (ofI N)"

lemma ofI_toI [simp]: "ofI (toI M) = M"
  by (induction M) simp_all

lemma toI_ofI [simp]: "toI (ofI P) = P"
  by (induction P) simp_all

theorem bij_toI: "bij toI"
  by (rule o_bij[of ofI]) (auto simp: fun_eq_iff)

text \<open>\<open>\<beta>\<close> under all congruences (capI's \<open>Beta\<close> with full compatibility).\<close>

inductive beta_full :: "Cap_Syntax.trm \<Rightarrow> Cap_Syntax.trm \<Rightarrow> bool" where
  Beta: "beta_full (Cap_Syntax.trm.App (Cap_Syntax.trm.Comp (Cap_Syntax.trm.Lam x M) L) N)
                   (Cap_Syntax.trm.Comp M (Cap_Syntax.trm.Extn N x L))"
| AppL: "beta_full M M' \<Longrightarrow> beta_full (Cap_Syntax.trm.App M N) (Cap_Syntax.trm.App M' N)"
| AppR: "beta_full N N' \<Longrightarrow> beta_full (Cap_Syntax.trm.App M N) (Cap_Syntax.trm.App M N')"
| CompL: "beta_full M M' \<Longrightarrow> beta_full (Cap_Syntax.trm.Comp M N) (Cap_Syntax.trm.Comp M' N)"
| CompR: "beta_full N N' \<Longrightarrow> beta_full (Cap_Syntax.trm.Comp M N) (Cap_Syntax.trm.Comp M N')"
| ExtnL: "beta_full M M' \<Longrightarrow> beta_full (Cap_Syntax.trm.Extn M x N) (Cap_Syntax.trm.Extn M' x N)"
| ExtnR: "beta_full N N' \<Longrightarrow> beta_full (Cap_Syntax.trm.Extn M x N) (Cap_Syntax.trm.Extn M x N')"
| Lam: "beta_full M M' \<Longrightarrow> beta_full (Cap_Syntax.trm.Lam x M) (Cap_Syntax.trm.Lam x M')"

lemma sig_red: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> toI M \<leadsto> toI N"
  by (induction rule: sig.induct) (auto intro: red.intros)

lemma beta_full_red: "beta_full M N \<Longrightarrow> toI M \<leadsto> toI N"
  by (induction rule: beta_full.induct) (auto intro: red.intros)

lemma red_sig_or_beta: "P \<leadsto> Q \<Longrightarrow> ofI P \<rightarrow>\<^sub>\<sigma> ofI Q \<or> beta_full (ofI P) (ofI Q)"
  by (induction rule: red.induct) (auto intro: sig.intros beta_full.intros)

theorem red_iff_sig_or_beta: "toI M \<leadsto> toI N \<longleftrightarrow> M \<rightarrow>\<^sub>\<sigma> N \<or> beta_full M N"
  using red_sig_or_beta[of "toI M" "toI N"] sig_red beta_full_red by auto

lemma beta_h_full: "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> beta_full M N"
  by (induction rule: beta_h.induct) (auto intro: beta_full.intros)

theorem wh_sub_red: "M \<rightarrow>\<^sub>w\<^sub>h N \<Longrightarrow> toI M \<leadsto> toI N"
  by (auto simp: wh_def dest: sig_red beta_h_full beta_full_red)

end
