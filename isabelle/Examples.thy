theory Examples
  imports Capture
begin

section \<open>Examples\<close>

text \<open>Variables are numbers: x = 0, y = 1, z = 2.\<close>

subsection \<open>Helper lemmas\<close>

lemma sn_Var: "sig_normal (Var x)"
  by (auto simp: normal_def elim: sig.cases)

lemma sn_Nil: "sig_normal Nil"
  by (auto simp: normal_def elim: sig.cases)

lemma sn_Lam: "sig_normal M \<Longrightarrow> sig_normal (Lam x M)"
  by (auto simp: normal_def elim: sig.cases)

lemma Typ_expand_steps: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N \<Longrightarrow> Typ N \<Longrightarrow> Typ M"
  unfolding Typ_def using subject_expansion_steps by blast

lemma no_SN_loop_aux: "SN_at wh a \<Longrightarrow> wh\<^sup>+\<^sup>+ a a \<Longrightarrow> False"
proof (induction rule: SN_at_induct)
  case (step a)
  from step.prems obtain b where ab: "wh a b" and ba: "wh\<^sup>*\<^sup>* b a"
    by (auto dest: tranclpD)
  have "wh\<^sup>+\<^sup>+ b b" using ba ab by (rule rtranclp_into_tranclp1)
  from step.IH[OF ab this] show False .
qed

lemma no_SN_loop: "wh\<^sup>+\<^sup>+ a a \<Longrightarrow> \<not> WHSN a"
  using no_SN_loop_aux by blast

subsection \<open>Clashes\<close>

lemma ex_bare_lam_app: "\<not> Typ (App (Lam 0 (Var 0)) (Var 1))"
proof -
  have c: "clash (App (Lam 0 (Var 0)) (Var 1))" by (rule clash.CLamApp[OF sn_Var sn_Var])
  show ?thesis by (rule clash_not_Typ[OF clash_WHNF[OF c] c])
qed

lemma ex_Nil_app: "sig_normal N \<Longrightarrow> \<not> Typ (App Nil N)"
proof -
  assume n: "sig_normal N"
  have c: "clash (App Nil N)" by (rule clash.CNil[OF n])
  show ?thesis by (rule clash_not_Typ[OF clash_WHNF[OF c] c])
qed

lemma ex_Nil_app_concrete: "\<not> Typ (App Nil (Lam 0 (Var 0)))"
  by (rule ex_Nil_app[OF sn_Lam[OF sn_Var]])

lemma ex_Var_Nil: "\<not> Typ (Comp (Var 0) Nil)"
  by (rule clash_not_Typ[OF clash_WHNF[OF clash_y_Nil] clash_y_Nil])

text \<open>\<open>x\<circ>((\<lambda>y.y)/x\<cdot>()) z\<close> reaches the clash \<open>(\<lambda>y.y) z\<close>.\<close>

lemma ex_lookup_clash:
  "\<not> Typ (App (Comp (Var 0) (Extn (Lam 1 (Var 1)) 0 Nil)) (Var 2))"
proof -
  have s: "sig (Comp (Var 0) (Extn (Lam 1 (Var 1)) 0 Nil)) (Lam 1 (Var 1))" by (rule sig.VarRef)
  have r: "App (Comp (Var 0) (Extn (Lam 1 (Var 1)) 0 Nil)) (Var 2) \<rightarrow>\<^sub>w\<^sub>h\<^sup>* App (Lam 1 (Var 1)) (Var 2)"
    by (rule r_into_rtranclp) (rule sig_imp_wh[OF sig.AppL[OF s]])
  have c: "clash (App (Lam 1 (Var 1)) (Var 2))" by (rule clash.CLamApp[OF sn_Var sn_Var])
  show ?thesis by (rule reach_clash_not_Typ[OF r clash_WHNF[OF c] c])
qed

subsection \<open>Typable terms\<close>

lemma ex_Lam_derivation: "CT [] \<turnstile> Lam 0 (Var 0) : Arr Om Om"
  by (rule TCode)

lemma ex_Lam_Typ: "Typ (Lam 0 (Var 0))"
  unfolding Typ_def using ex_Lam_derivation by force

lemma ex_Nil_derivation: "CT [] \<turnstile> Nil : Env [] True"
  by (rule TNil)

lemma ex_Nil_Typ: "Typ Nil"
  unfolding Typ_def using ex_Nil_derivation by force

lemma ex_Clo_derivation: "CT [] \<turnstile> Comp (Lam 0 (Var 0)) Nil : Arr Om Om"
  by (rule TComp[OF TNil TCode])

lemma ex_Clo_Typ: "Typ (Comp (Lam 0 (Var 0)) Nil)"
  unfolding Typ_def using ex_Clo_derivation by force

lemma ex_Clo_Typ': "Typ (Comp (Lam 0 (Var 0)) Nil)"
  by (rule val_Typ[OF val.VClo[OF sn_Var sn_Nil]])

text \<open>\<open>((\<lambda>x.x)\<circ>()) z\<close> reduces by \<open>\<beta>\<close> and \<open>\<sigma>\<close> to \<open>z\<close>.\<close>

lemma ex_Clo_app_steps:
  "App (Comp (Lam 0 (Var 0)) Nil) (Var 2) \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Var 2"
proof -
  have "App (Comp (Lam 0 (Var 0)) Nil) (Var 2) \<rightarrow>\<^sub>\<beta> Comp (Var 0) (Extn (Var 2) 0 Nil)"
    by (rule beta_h.Beta)
  then have b: "wh (App (Comp (Lam 0 (Var 0)) Nil) (Var 2)) (Comp (Var 0) (Extn (Var 2) 0 Nil))"
    by (rule beta_h_imp_wh)
  have c: "wh (Comp (Var 0) (Extn (Var 2) 0 Nil)) (Var 2)" using sig.VarRef by (rule sig_imp_wh)
  from c have c': "wh\<^sup>*\<^sup>* (Comp (Var 0) (Extn (Var 2) 0 Nil)) (Var 2)" by (rule r_into_rtranclp)
  show ?thesis by (rule converse_rtranclp_into_rtranclp[OF b c'])
qed

lemma ex_Clo_app_Typ: "Typ (App (Comp (Lam 0 (Var 0)) Nil) (Var 2))"
  by (rule Typ_expand_steps[OF ex_Clo_app_steps neu_Typ[OF neu.NVar]])

subsection \<open>The diverging term \<open>\<Omega>\<close>\<close>

abbreviation Cw :: trm where
  "Cw \<equiv> Comp (Lam 0 (App (Var 0) (Var 0))) Nil"

abbreviation Omega :: trm where
  "Omega \<equiv> App Cw Cw"

lemma Omega_loop: "wh\<^sup>+\<^sup>+ Omega Omega"
proof -
  let ?E = "Extn Cw 0 Nil"
  have s1: "wh Omega (Comp (App (Var 0) (Var 0)) ?E)"
    by (rule beta_h_imp_wh[OF beta_h.Beta])
  have s2: "wh (Comp (App (Var 0) (Var 0)) ?E) (App (Comp (Var 0) ?E) (Comp (Var 0) ?E))"
    by (rule sig_imp_wh[OF sig.DApp])
  have v: "sig (Comp (Var 0) ?E) Cw" by (rule sig.VarRef)
  have s3: "wh (App (Comp (Var 0) ?E) (Comp (Var 0) ?E)) (App Cw (Comp (Var 0) ?E))"
    by (rule sig_imp_wh[OF sig.AppL[OF v]])
  have s4: "wh (App Cw (Comp (Var 0) ?E)) Omega"
    by (rule sig_imp_wh[OF sig.AppR[OF v]])
  have t4: "wh\<^sup>+\<^sup>+ (App Cw (Comp (Var 0) ?E)) Omega" by (rule tranclp.r_into_trancl[of wh, OF s4])
  have t3: "wh\<^sup>+\<^sup>+ (App (Comp (Var 0) ?E) (Comp (Var 0) ?E)) Omega"
    by (rule tranclp_into_tranclp2[OF s3 t4])
  have t2: "wh\<^sup>+\<^sup>+ (Comp (App (Var 0) (Var 0)) ?E) Omega" by (rule tranclp_into_tranclp2[OF s2 t3])
  show ?thesis by (rule tranclp_into_tranclp2[OF s1 t2])
qed

lemma Omega_not_Typ: "\<not> Typ Omega"
proof
  assume "Typ Omega"
  then have "CFWHSN Omega" using main_characterization_full by blast
  then have "WHSN Omega" by (simp add: CFWHSN_def)
  with no_SN_loop[OF Omega_loop] show False by blast
qed

subsection \<open>Capture examples\<close>

text \<open>
  \<open>E = (V/y)\<cdot>((W/z)\<cdot>())\<close> with \<open>V = \<lambda>x.x\<close>, \<open>W = \<lambda>y.y\<close> (y = 1, z = 2).
\<close>

abbreviation CapEnv :: trm where
  "CapEnv \<equiv> Extn (Lam 0 (Var 0)) 1 (Extn (Lam 1 (Var 1)) 2 Nil)"

lemma ex_cap_typed: "CT [(2, A)] \<turnstile> cap [2] : Env [(2, A)] True"
proof -
  have p: "provides (CT [(2, A)]) [(2, A)]" by (simp add: fields_le_def sub.s_refl)
  from cap_typed_provides[OF p, of "[2]"] show ?thesis by simp
qed

lemma ss_ExtnL: "sig\<^sup>*\<^sup>* M N \<Longrightarrow> sig\<^sup>*\<^sup>* (Extn M x L) (Extn N x L)"
  by (induction rule: rtranclp.induct) (auto intro: sig.ExtnL rtranclp.intros)

lemma ex_cap_reduces:
  "sig\<^sup>*\<^sup>* (Comp (cap [2]) CapEnv) (Extn (Lam 1 (Var 1)) 2 Nil)"
proof -
  have a: "sig\<^sup>*\<^sup>* (Comp (cap [2]) CapEnv) (Extn (Comp (Var 2) CapEnv) 2 Nil)"
    using cap_comp_sigma[of "[2]" CapEnv] by simp
  have s: "sig (Comp (Var 2) CapEnv) (Comp (Var 2) (Extn (Lam 1 (Var 1)) 2 Nil))"
    by (rule sig.VarSkip) simp
  have t: "sig (Comp (Var 2) (Extn (Lam 1 (Var 1)) 2 Nil)) (Lam 1 (Var 1))" by (rule sig.VarRef)
  have "sig\<^sup>*\<^sup>* (Comp (Var 2) CapEnv) (Lam 1 (Var 1))"
    by (rule converse_rtranclp_into_rtranclp[OF s ss1[OF t]])
  then have "sig\<^sup>*\<^sup>* (Extn (Comp (Var 2) CapEnv) 2 Nil) (Extn (Lam 1 (Var 1)) 2 Nil)"
    by (rule ss_ExtnL)
  with a show ?thesis by (rule ss_trans)
qed

text \<open>The unreachable \<open>y\<close>: \<open>y\<circ>((cap [z])\<circ>E)\<close> is a clash, so not typable.\<close>

lemma ex_cap_uncaptured: "\<not> Typ (Comp (Var 1) (Comp (cap [2]) CapEnv))"
  by (rule cap_comp_uncaptured_not_Typ) simp

lemma ex_cap_uncaptured_plain: "\<not> Typ (Comp (Var 1) (cap [2]))"
  by (rule cap_uncaptured_not_Typ) simp

text \<open>The captured \<open>z\<close>: \<open>z\<circ>((cap [z])\<circ>E)\<close> reaches the value \<open>W\<close>.\<close>

lemma ex_cap_captured_steps:
  "Comp (Var 2) CapEnv \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Lam 1 (Var 1)"
proof -
  have s: "Comp (Var 2) CapEnv \<rightarrow>\<^sub>\<sigma> Comp (Var 2) (Extn (Lam 1 (Var 1)) 2 Nil)"
    by (rule sig.VarSkip) simp
  have t: "Comp (Var 2) (Extn (Lam 1 (Var 1)) 2 Nil) \<rightarrow>\<^sub>\<sigma> Lam 1 (Var 1)" by (rule sig.VarRef)
  have s': "wh (Comp (Var 2) CapEnv) (Comp (Var 2) (Extn (Lam 1 (Var 1)) 2 Nil))"
    by (rule sig_imp_wh[OF s])
  have t': "wh\<^sup>*\<^sup>* (Comp (Var 2) (Extn (Lam 1 (Var 1)) 2 Nil)) (Lam 1 (Var 1))"
    by (rule r_into_rtranclp[of wh, OF sig_imp_wh[OF t]])
  show ?thesis by (rule converse_rtranclp_into_rtranclp[OF s' t'])
qed

lemma ex_cap_captured:
  "Comp (Var 2) (Comp (cap [2]) CapEnv) \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Lam 1 (Var 1)"
  and "Typ (Comp (Var 2) (Comp (cap [2]) CapEnv))"
  using cap_captured_reaches_value[of 2 "[2]" CapEnv "Lam 1 (Var 1)", OF _ ex_cap_captured_steps
        val.VLam[OF sn_Var]]
  by simp_all

lemma ex_cap_captured_plain: "Typ (Comp (Var 2) (cap [2]))"
  by (rule cap_captured_Typ) simp

end
