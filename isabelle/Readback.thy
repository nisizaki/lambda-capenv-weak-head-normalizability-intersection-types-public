theory Readback
  imports Uniform Lambda
begin

section \<open>Readback of pure terms\<close>

text \<open>
  \<open>pure\<close> terms contain only \<open>Var\<close>, \<open>Lam\<close> and \<open>App\<close>.  Compared with the \<open>\<lambda>\<^sub>e\<^sub>n\<^sub>v\<close>
  readback, the empty environment \<open>Nil\<close> reads back every variable as \<open>junk\<close>
  (there is no \<open>id\<close>).
\<close>

fun pure :: "trm \<Rightarrow> bool" where
  "pure (Var x) = True"
| "pure (Lam x M) = pure M"
| "pure (App M N) = (pure M \<and> pure N)"
| "pure Nil = False"
| "pure (Extn M x L) = False"
| "pure (Comp M L) = False"

text \<open>Free variables of pure terms (the value on non-pure terms is irrelevant).\<close>

fun fvp :: "trm \<Rightarrow> var set" where
  "fvp (Var x) = {x}"
| "fvp (Lam x M) = fvp M - {x}"
| "fvp (App M N) = fvp M \<union> fvp N"
| "fvp Nil = {}"
| "fvp (Extn M x L) = {}"
| "fvp (Comp M L) = {}"

definition junk :: dB where "junk = DAbs (DVar 0)"

lemma subst_junk [simp]: "junk[s/k] = junk"
  by (simp add: junk_def)

fun rb :: "trm \<Rightarrow> (var \<Rightarrow> dB) \<Rightarrow> dB" and rbe :: "trm \<Rightarrow> (var \<Rightarrow> dB) \<Rightarrow> (var \<Rightarrow> dB)" where
  "rb (Var x) \<rho> = \<rho> x"
| "rb (Lam x M) \<rho> = DAbs (rb M ((\<lambda>y. lift (\<rho> y) 0)(x := DVar 0)))"
| "rb (App M N) \<rho> = DApp (rb M \<rho>) (rb N \<rho>)"
| "rb (Comp M L) \<rho> = rb M (rbe L \<rho>)"
| "rb Nil \<rho> = junk"
| "rb (Extn M x L) \<rho> = junk"
| "rbe (Var x) \<rho> = \<rho>"
| "rbe (Lam x M) \<rho> = \<rho>"
| "rbe (App M N) \<rho> = \<rho>"
| "rbe (Comp L1 L2) \<rho> = rbe L1 (rbe L2 \<rho>)"
| "rbe Nil \<rho> = (\<lambda>y. junk)"
| "rbe (Extn M x L) \<rho> = (rbe L \<rho>)(x := rb M \<rho>)"

lemma rb_subst:
  "(\<forall>\<sigma> s k. (rb M \<sigma>)[s/k] = rb M (\<lambda>y. (\<sigma> y)[s/k])) \<and>
   (\<forall>\<sigma> s k. rbe M (\<lambda>y. (\<sigma> y)[s/k]) = (\<lambda>y. (rbe M \<sigma> y)[s/k]))"
proof (induction M)
  case (Var x)
  then show ?case by simp
next
  case (Lam x M)
  have "(rb (Lam x M) \<sigma>)[s/k] = rb (Lam x M) (\<lambda>y. (\<sigma> y)[s/k])" for \<sigma> s k
  proof -
    have fe: "(\<lambda>y. (((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)) y)[lift s 0 / k + 1])
            = (\<lambda>y. lift ((\<sigma> y)[s/k]) 0)(x := DVar 0)"
      by (rule ext) (simp add: lift_subst_lt)
    have "(rb (Lam x M) \<sigma>)[s/k]
        = DAbs ((rb M ((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)))[lift s 0 / k + 1])"
      by simp
    also have "\<dots> = DAbs (rb M (\<lambda>y. (((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)) y)[lift s 0 / k + 1]))"
      using Lam.IH by simp
    also have "\<dots> = rb (Lam x M) (\<lambda>y. (\<sigma> y)[s/k])"
      by (simp only: fe rb.simps)
    finally show ?thesis .
  qed
  then show ?case by simp
next
  case (App M N)
  then show ?case by simp
next
  case Nil
  then show ?case by (simp add: fun_eq_iff)
next
  case (Extn M x L)
  have "rbe (Extn M x L) (\<lambda>y. (\<sigma> y)[s/k]) = (\<lambda>y. (rbe (Extn M x L) \<sigma> y)[s/k])" for \<sigma> s k
    using Extn.IH by (auto intro!: ext)
  then show ?case by simp
next
  case (Comp M L)
  then show ?case by simp
qed

lemma beta_rb:
  "(rb M ((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)))[t/0] = rb M (\<sigma>(x := t))"
proof -
  have "(\<lambda>y. (((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)) y)[t/0]) = \<sigma>(x := t)"
    by (rule ext) simp
  then show ?thesis
    using rb_subst[of M] by simp
qed

text \<open>Lemma 11.1: readback of a pure term depends only on its free variables.\<close>

lemma rb_fv:
  "pure M \<Longrightarrow> (\<forall>y \<in> fvp M. \<rho> y = \<rho>' y) \<Longrightarrow> rb M \<rho> = rb M \<rho>'"
proof (induction M arbitrary: \<rho> \<rho>')
  case (Lam x M)
  have "((\<lambda>y. lift (\<rho> y) 0)(x := DVar 0)) y = ((\<lambda>y. lift (\<rho>' y) 0)(x := DVar 0)) y"
    if "y \<in> fvp M" for y
    using that Lam.prems by (cases "y = x") auto
  then show ?case using Lam.prems Lam.IH by simp
next
  case (App M N)
  then show ?case by simp
qed simp_all

section \<open>Evaluation results: the sets \<open>SS\<close> and \<open>EN\<close>\<close>

fun edom :: "trm \<Rightarrow> var set" where
  "edom Nil = {}"
| "edom (Extn S x E) = insert x (edom E)"
| "edom (Var x) = {}"
| "edom (Lam x M) = {}"
| "edom (App M N) = {}"
| "edom (Comp M N) = {}"

fun elk :: "trm \<Rightarrow> var \<Rightarrow> trm option" where
  "elk Nil y = None"
| "elk (Extn S x E) y = (if x = y then Some S else elk E y)"
| "elk (Var x) y = None"
| "elk (Lam x M) y = None"
| "elk (App M N) y = None"
| "elk (Comp M N) y = None"

inductive SS :: "trm \<Rightarrow> bool" and EN :: "trm \<Rightarrow> bool" where
  SVar: "SS (Var x)"
| SApp: "SS S1 \<Longrightarrow> SS S2 \<Longrightarrow> SS (App S1 S2)"
| SClo: "pure P \<Longrightarrow> EN E \<Longrightarrow> fvp (Lam x P) \<subseteq> edom E \<Longrightarrow> SS (Comp (Lam x P) E)"
| ENil: "EN Nil"
| EExt: "SS S \<Longrightarrow> EN E \<Longrightarrow> EN (Extn S x E)"

fun eval :: "trm \<Rightarrow> trm \<Rightarrow> trm" where
  "eval (Var y) E = (case elk E y of Some S \<Rightarrow> S | None \<Rightarrow> Nil)"
| "eval (App P Q) E = App (eval P E) (eval Q E)"
| "eval (Lam x P) E = Comp (Lam x P) E"
| "eval Nil E = Nil"
| "eval (Extn M x L) E = Nil"
| "eval (Comp M L) E = Nil"

subsection \<open>\<open>\<sigma>\<close>-normality (Lemma 11.2(1))\<close>

lemma Var_sn: "sig_normal (Var x)"
  by (auto simp: normal_def elim: sig.cases)

lemma Nil_sn: "sig_normal Nil"
  by (auto simp: normal_def elim: sig.cases)

lemma App_sn: "sig_normal M \<Longrightarrow> sig_normal N \<Longrightarrow> sig_normal (App M N)"
  by (auto simp: normal_def elim: sig.cases)

lemma Extn_sn: "sig_normal M \<Longrightarrow> sig_normal N \<Longrightarrow> sig_normal (Extn M x N)"
  by (auto simp: normal_def elim: sig.cases)

lemma Lam_sn: "sig_normal M \<Longrightarrow> sig_normal (Lam x M)"
  by (auto simp: normal_def elim: sig.cases)

lemma Clo_sn: "sig_normal M \<Longrightarrow> sig_normal L \<Longrightarrow> sig_normal (Comp (Lam x M) L)"
proof (rule normalI)
  assume m: "sig_normal M" and l: "sig_normal L"
  fix b
  show "\<not> Comp (Lam x M) L \<rightarrow>\<^sub>\<sigma> b"
  proof
    assume "Comp (Lam x M) L \<rightarrow>\<^sub>\<sigma> b"
    then show False
    proof (cases rule: sig.cases)
      case CompL
      then show False using m CompL by (auto simp: normal_def elim: sig.cases)
    next
      case CompR
      then show False using l CompR by (auto simp: normal_def)
    qed
  qed
qed

lemma pure_sn: "pure M \<Longrightarrow> sig_normal M"
  by (induction M) (auto simp: Var_sn Lam_sn App_sn)

lemma SS_sn: "SS S \<Longrightarrow> sig_normal S" and EN_sn: "EN E \<Longrightarrow> sig_normal E"
proof (induction rule: SS_EN.inducts)
  case (SVar x)
  then show ?case by (simp add: Var_sn)
next
  case (SApp S1 S2)
  then show ?case by (simp add: App_sn)
next
  case (SClo P E x)
  then show ?case by (simp add: Clo_sn Lam_sn pure_sn)
next
  case ENil
  then show ?case by (simp add: Nil_sn)
next
  case (EExt S E x)
  then show ?case by (simp add: Extn_sn)
qed

subsection \<open>Evaluation (Lemma 11.2(2),(3))\<close>

lemma sig_steps_AppR': "sig\<^sup>*\<^sup>* N N' \<Longrightarrow> sig\<^sup>*\<^sup>* (App M N) (App M N')"
  by (rule steps_lift[of sig sig "\<lambda>P. App M P"]) (auto intro: sig.AppR)

lemma sig_steps_AppL': "sig\<^sup>*\<^sup>* M M' \<Longrightarrow> sig\<^sup>*\<^sup>* (App M N) (App M' N)"
  by (rule steps_lift[of sig sig "\<lambda>P. App P N"]) (auto intro: sig.AppL)

lemma elk_SS: "SS S \<Longrightarrow> True" and
  elk_EN: "EN E \<Longrightarrow> y \<in> edom E \<Longrightarrow>
     \<exists>S. elk E y = Some S \<and> SS S \<and> sig\<^sup>*\<^sup>* (Comp (Var y) E) S \<and> (\<forall>\<rho>. rbe E \<rho> y = rb S \<rho>)"
proof (induction rule: SS_EN.inducts)
  case (EExt S E x)
  show ?case
  proof (cases "x = y")
    case True
    have "Comp (Var y) (Extn S x E) \<rightarrow>\<^sub>\<sigma> S" using True sig.VarRef by blast
    then show ?thesis using True EExt.hyps by auto
  next
    case False
    with EExt.prems have "y \<in> edom E" by simp
    from EExt.IH(2)[OF this] obtain S' where
      s: "elk E y = Some S'" "SS S'" "sig\<^sup>*\<^sup>* (Comp (Var y) E) S'"
      "\<forall>\<rho>. rbe E \<rho> y = rb S' \<rho>" by blast
    have st: "Comp (Var y) (Extn S x E) \<rightarrow>\<^sub>\<sigma> Comp (Var y) E"
      using False sig.VarSkip by blast
    have "sig\<^sup>*\<^sup>* (Comp (Var y) (Extn S x E)) S'"
      using st s(3) by (rule converse_rtranclp_into_rtranclp)
    then show ?thesis using False s by auto
  qed
qed simp_all

lemma eval_main:
  "pure P \<Longrightarrow> EN E \<Longrightarrow> fvp P \<subseteq> edom E \<Longrightarrow>
     SS (eval P E) \<and> sig\<^sup>*\<^sup>* (Comp P E) (eval P E) \<and> (\<forall>\<rho>. rb (Comp P E) \<rho> = rb (eval P E) \<rho>)"
proof (induction P)
  case (Var y)
  from Var.prems have "y \<in> edom E" by simp
  from elk_EN[OF Var.prems(2) this] obtain S where
    "elk E y = Some S" "SS S" "sig\<^sup>*\<^sup>* (Comp (Var y) E) S" "\<forall>\<rho>. rbe E \<rho> y = rb S \<rho>" by blast
  then show ?case by simp
next
  case (Lam x P)
  have "SS (Comp (Lam x P) E)"
    using Lam.prems by (intro SClo) simp_all
  then show ?case by simp
next
  case (App P Q)
  from App.prems have pp: "pure P" "pure Q" and fv: "fvp P \<subseteq> edom E" "fvp Q \<subseteq> edom E"
    by simp_all
  from App.IH(1)[OF pp(1) App.prems(2) fv(1)] have 1: "SS (eval P E)"
    "sig\<^sup>*\<^sup>* (Comp P E) (eval P E)" "\<forall>\<rho>. rb (Comp P E) \<rho> = rb (eval P E) \<rho>" by blast+
  from App.IH(2)[OF pp(2) App.prems(2) fv(2)] have 2: "SS (eval Q E)"
    "sig\<^sup>*\<^sup>* (Comp Q E) (eval Q E)" "\<forall>\<rho>. rb (Comp Q E) \<rho> = rb (eval Q E) \<rho>" by blast+
  have s0: "Comp (App P Q) E \<rightarrow>\<^sub>\<sigma> App (Comp P E) (Comp Q E)" by (rule sig.DApp)
  have s1: "sig\<^sup>*\<^sup>* (App (Comp P E) (Comp Q E)) (App (eval P E) (Comp Q E))"
    using sig_steps_AppL'[OF 1(2)] .
  have s2: "sig\<^sup>*\<^sup>* (App (eval P E) (Comp Q E)) (App (eval P E) (eval Q E))"
    using sig_steps_AppR'[OF 2(2)] .
  have "sig\<^sup>*\<^sup>* (Comp (App P Q) E) (App (eval P E) (eval Q E))"
    using s0 s1 s2 by (meson converse_rtranclp_into_rtranclp rtranclp_trans)
  then show ?case using 1 2 by (auto intro: SApp)
qed simp_all

section \<open>Head steps of evaluation results (Lemma 11.3)\<close>

inductive hneu :: "dB \<Rightarrow> bool" where
  "hneu (DVar i)"
| "hneu s \<Longrightarrow> hneu (DApp s t)"

lemma hneu_normal: "hneu s \<Longrightarrow> normal hred s"
proof (induction rule: hneu.induct)
  case (1 i)
  then show ?case by (auto simp: normal_def elim: hred.cases)
next
  case (2 s t)
  then show ?case by (auto simp: normal_def elim: hred.cases hneu.cases)
qed

lemma DAbs_normal: "normal hred (DAbs s)"
  by (auto simp: normal_def elim: hred.cases)

lemma SS_Clo_inv:
  assumes "SS (Comp (Lam x P) E)"
  shows "pure P \<and> EN E \<and> fvp (Lam x P) \<subseteq> edom E"
  using assms by (cases rule: SS.cases) auto

lemma head_step: "SS S \<Longrightarrow>
     (neu S \<and> hneu (rb S DVar)) \<or> (val S \<and> normal hred (rb S DVar)) \<or>
     (\<exists>S' S''. S \<rightarrow>\<^sub>\<beta> S' \<and> sig\<^sup>*\<^sup>* S' S'' \<and> SS S'' \<and> rb S DVar \<rightarrow>\<^sub>h rb S'' DVar)"
  and head_EN: "EN E \<Longrightarrow> True"
proof (induction rule: SS_EN.inducts)
  case (SVar x)
  then show ?case by (auto intro: neu.NVar hneu.intros)
next
  case (SClo P E x)
  have "val (Comp (Lam x P) E)"
    using SClo pure_sn EN_sn by (intro VClo) simp_all
  then show ?case by (auto simp: DAbs_normal)
next
  case (SApp S1 S2)
  have sn2: "sig_normal S2" using SApp.hyps(2) SS_sn by blast
  show ?case
  proof (cases "\<exists>x P E. S1 = Comp (Lam x P) E")
    case True
    then obtain x P E where s1: "S1 = Comp (Lam x P) E" by blast
    from SApp.hyps(1) s1 have inv: "pure P" "EN E" "fvp (Lam x P) \<subseteq> edom E"
      using SS_Clo_inv by blast+
    let ?E' = "Extn S2 x E"
    have en': "EN ?E'" by (rule EExt[OF SApp.hyps(2) inv(2)])
    have fv': "fvp P \<subseteq> edom ?E'" using inv(3) by auto
    from eval_main[OF inv(1) en' fv'] have ev:
      "SS (eval P ?E')" "sig\<^sup>*\<^sup>* (Comp P ?E') (eval P ?E')"
      "\<forall>\<rho>. rb (Comp P ?E') \<rho> = rb (eval P ?E') \<rho>" by blast+
    have b: "App S1 S2 \<rightarrow>\<^sub>\<beta> Comp P ?E'" using s1 beta_h.Beta by blast
    have "rb (App S1 S2) DVar \<rightarrow>\<^sub>h rb (eval P ?E') DVar"
    proof -
      have "rb (App S1 S2) DVar =
        DApp (DAbs (rb P ((\<lambda>y. lift (rbe E DVar y) 0)(x := DVar 0)))) (rb S2 DVar)"
        by (simp add: s1)
      moreover have "DApp (DAbs (rb P ((\<lambda>y. lift (rbe E DVar y) 0)(x := DVar 0)))) (rb S2 DVar)
          \<rightarrow>\<^sub>h (rb P ((\<lambda>y. lift (rbe E DVar y) 0)(x := DVar 0)))[rb S2 DVar/0]"
        by (rule hbeta)
      moreover have "(rb P ((\<lambda>y. lift (rbe E DVar y) 0)(x := DVar 0)))[rb S2 DVar/0]
          = rb (eval P ?E') DVar"
        using beta_rb[of P "rbe E DVar" x "rb S2 DVar"] ev(3) by simp
      ultimately show ?thesis by simp
    qed
    then show ?thesis using b ev(1,2) by blast
  next
    case False
    have noval: "\<not> val S1"
      using SApp.hyps(1) False by (cases rule: SS.cases) (auto elim: val.cases)
    from SApp.IH(1) noval show ?thesis
    proof (elim disjE conjE)
      assume n: "neu S1" and h: "hneu (rb S1 DVar)"
      have "neu (App S1 S2)" using n sn2 by (rule neu.NApp)
      moreover have "hneu (rb (App S1 S2) DVar)" using h by (simp add: hneu.intros(2))
      ultimately show ?thesis by blast
    next
      assume "val S1" with noval show ?thesis by blast
    next
      assume "\<exists>S' S''. S1 \<rightarrow>\<^sub>\<beta> S' \<and> sig\<^sup>*\<^sup>* S' S'' \<and> SS S'' \<and> rb S1 DVar \<rightarrow>\<^sub>h rb S'' DVar"
      then obtain S' S'' where b: "S1 \<rightarrow>\<^sub>\<beta> S'" and r: "sig\<^sup>*\<^sup>* S' S''" and
        ss: "SS S''" and h: "rb S1 DVar \<rightarrow>\<^sub>h rb S'' DVar" by blast
      have "App S1 S2 \<rightarrow>\<^sub>\<beta> App S' S2" using b by (rule beta_h.AppL)
      moreover have "sig\<^sup>*\<^sup>* (App S' S2) (App S'' S2)" using r by (rule sig_steps_AppL')
      moreover have "SS (App S'' S2)" using ss SApp.hyps(2) by (rule SS_EN.SApp)
      moreover have "rb (App S1 S2) DVar \<rightarrow>\<^sub>h rb (App S'' S2) DVar"
        using h by (simp add: happ)
      ultimately show ?thesis by blast
    qed
  qed
qed simp_all

section \<open>Relating the two calculi (Lemma 11.4)\<close>

lemma lam_WHN_back: "t \<rightarrow>\<^sub>h u \<Longrightarrow> lam_WHN u \<Longrightarrow> lam_WHN t"
  unfolding lam_WHN_def by (meson converse_rtranclp_into_rtranclp)

lemma hdist_SS_CFWHN: "hdist t n \<Longrightarrow> SS S \<Longrightarrow> t = rb S DVar \<Longrightarrow> CFWHN S"
proof (induction arbitrary: S rule: hdist.induct)
  case (hd0 t)
  from head_step[OF hd0.prems(1)] show ?case
  proof (elim disjE conjE)
    assume "neu S" then show ?thesis by (rule neu_CFWHN)
  next
    assume "val S" then show ?thesis by (rule val_CFWHN)
  next
    assume "\<exists>S' S''. S \<rightarrow>\<^sub>\<beta> S' \<and> sig\<^sup>*\<^sup>* S' S'' \<and> SS S'' \<and> rb S DVar \<rightarrow>\<^sub>h rb S'' DVar"
    then obtain S'' where "rb S DVar \<rightarrow>\<^sub>h rb S'' DVar" by blast
    with hd0.hyps hd0.prems(2) show ?thesis by (auto simp: normal_def)
  qed
next
  case (hdS t u n)
  from head_step[OF hdS.prems(1)] show ?case
  proof (elim disjE conjE)
    assume "neu S" "hneu (rb S DVar)"
    then have "normal hred (rb S DVar)" by (simp add: hneu_normal)
    with hdS.hyps(1) hdS.prems(2) show ?thesis by (auto simp: normal_def)
  next
    assume "val S" "normal hred (rb S DVar)"
    with hdS.hyps(1) hdS.prems(2) show ?thesis by (auto simp: normal_def)
  next
    assume "\<exists>S' S''. S \<rightarrow>\<^sub>\<beta> S' \<and> sig\<^sup>*\<^sup>* S' S'' \<and> SS S'' \<and> rb S DVar \<rightarrow>\<^sub>h rb S'' DVar"
    then obtain S' S'' where b: "S \<rightarrow>\<^sub>\<beta> S'" and r: "sig\<^sup>*\<^sup>* S' S''" and ss: "SS S''"
      and h: "rb S DVar \<rightarrow>\<^sub>h rb S'' DVar" by blast
    from hred_det h hdS.hyps(1) hdS.prems(2) have "u = rb S'' DVar" by metis
    from hdS.IH[OF ss this] have "CFWHN S''" .
    moreover have "S \<rightarrow>\<^sub>w\<^sub>h\<^sup>* S''"
    proof -
      have "S \<rightarrow>\<^sub>w\<^sub>h S'" using b by (rule beta_h_imp_wh)
      moreover have "S' \<rightarrow>\<^sub>w\<^sub>h\<^sup>* S''" using r by (rule sig_steps_wh)
      ultimately show ?thesis by (rule converse_rtranclp_into_rtranclp)
    qed
    ultimately show ?thesis by (rule CFWHN_back_steps[rotated])
  qed
qed

lemma cd_sig_steps: "sig\<^sup>*\<^sup>* M M' \<Longrightarrow> cd M n E \<Longrightarrow> cd M' n E"
  by (induction rule: rtranclp_induct) (auto intro: cd_fwd_sig)

lemma cd_Suc_inv: "cd S (Suc m) N \<Longrightarrow> \<exists>N'. snf S \<rightarrow>\<^sub>\<beta> N' \<and> cd N' m N"
  by (cases rule: cd.cases) auto

lemma cd_SS_lam_WHN: "cd S k N \<Longrightarrow> SS S \<Longrightarrow> lam_WHN (rb S DVar)"
proof (induction k arbitrary: S)
  case 0
  from head_step[OF "0.prems"(2)] show ?case
  proof (elim disjE conjE)
    assume "neu S" "hneu (rb S DVar)"
    then show ?thesis by (auto simp: lam_WHN_def hneu_normal)
  next
    assume "val S" "normal hred (rb S DVar)"
    then show ?thesis by (auto simp: lam_WHN_def)
  next
    assume "\<exists>S' S''. S \<rightarrow>\<^sub>\<beta> S' \<and> sig\<^sup>*\<^sup>* S' S'' \<and> SS S'' \<and> rb S DVar \<rightarrow>\<^sub>h rb S'' DVar"
    then obtain S' where "S \<rightarrow>\<^sub>\<beta> S'" by blast
    from cd_fwd_beta[OF this "0.prems"(1)] show ?thesis by simp
  qed
next
  case (Suc m)
  from head_step[OF Suc.prems(2)] show ?case
  proof (elim disjE conjE)
    assume "neu S" "hneu (rb S DVar)"
    then have w: "WHNF S" by (simp add: neu_WHNF)
    have sn: "snf S = S" using snf_unique[OF rtranclp.rtrancl_refl SS_sn[OF Suc.prems(2)]] .
    from cd_Suc_inv[OF Suc.prems(1)] obtain N' where "snf S \<rightarrow>\<^sub>\<beta> N'" by blast
    then have "S \<rightarrow>\<^sub>\<beta> N'" using sn by simp
    then show ?thesis using w by (auto simp: normal_def wh_def)
  next
    assume "val S" "normal hred (rb S DVar)"
    then have w: "WHNF S" by (simp add: val_WHNF)
    have sn: "snf S = S" using snf_unique[OF rtranclp.rtrancl_refl SS_sn[OF Suc.prems(2)]] .
    from cd_Suc_inv[OF Suc.prems(1)] obtain N' where "snf S \<rightarrow>\<^sub>\<beta> N'" by blast
    then have "S \<rightarrow>\<^sub>\<beta> N'" using sn by simp
    then show ?thesis using w by (auto simp: normal_def wh_def)
  next
    assume "\<exists>S' S''. S \<rightarrow>\<^sub>\<beta> S' \<and> sig\<^sup>*\<^sup>* S' S'' \<and> SS S'' \<and> rb S DVar \<rightarrow>\<^sub>h rb S'' DVar"
    then obtain S' S'' where b: "S \<rightarrow>\<^sub>\<beta> S'" and r: "sig\<^sup>*\<^sup>* S' S''" and ss: "SS S''"
      and h: "rb S DVar \<rightarrow>\<^sub>h rb S'' DVar" by blast
    from cd_fwd_beta[OF b Suc.prems(1)] obtain m' where "Suc m = Suc m'" "cd S' m' N" by blast
    then have "cd S'' m N" using cd_sig_steps[OF r] by simp
    from Suc.IH[OF this ss] have "lam_WHN (rb S'' DVar)" .
    with h show ?thesis by (rule lam_WHN_back)
  qed
qed

lemma SS_CFWHN_iff: "SS S \<Longrightarrow> lam_WHN (rb S DVar) \<longleftrightarrow> CFWHN S"
proof
  assume "SS S" "lam_WHN (rb S DVar)"
  then obtain n where "hdist (rb S DVar) n" using lam_WHN_hdist by blast
  then show "CFWHN S" using \<open>SS S\<close> hdist_SS_CFWHN by blast
next
  assume s: "SS S" "CFWHN S"
  then obtain N where r: "S \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" and n: "WHNF N" by (auto simp: CFWHN_def)
  from steps_cd[OF r n] obtain k where "cd S k N" by blast
  then show "lam_WHN (rb S DVar)" using s(1) cd_SS_lam_WHN by blast
qed

section \<open>Relation to pure \<open>\<lambda>\<close>-terms\<close>

lemma cap_Cons: "cap (x # xs) = Extn (Var x) x (cap xs)"
  by (simp add: cap_def)

lemma cap_Nil: "cap [] = Nil"
  by (simp add: cap_def)

lemma cap_EN: "EN (cap xs)"
  by (induction xs) (auto simp: cap_Cons cap_Nil intro: ENil EExt SVar)

lemma cap_edom: "edom (cap xs) = set xs"
  by (induction xs) (auto simp: cap_Cons cap_Nil)

lemma cap_rbe: "y \<in> set xs \<Longrightarrow> rbe (cap xs) DVar y = DVar y"
  by (induction xs) (auto simp: cap_Cons cap_Nil)

lemma Pure_rb:
  assumes "pure M" "fvp M \<subseteq> set xs"
  shows "rb (Comp M (cap xs)) DVar = rb M DVar"
proof -
  have "\<forall>y \<in> fvp M. rbe (cap xs) DVar y = DVar y"
    using assms(2) cap_rbe by blast
  then show ?thesis using assms(1) rb_fv[of M "rbe (cap xs) DVar" DVar] by simp
qed

theorem Pure_lam_CFWHN:
  assumes "pure M" "fvp M \<subseteq> set xs"
  shows "lam_WHN (rb M DVar) \<longleftrightarrow> CFWHN (Comp M (cap xs))"
proof -
  have fv: "fvp M \<subseteq> edom (cap xs)" using assms(2) by (simp add: cap_edom)
  from eval_main[OF assms(1) cap_EN fv] have ev:
    "SS (eval M (cap xs))" "sig\<^sup>*\<^sup>* (Comp M (cap xs)) (eval M (cap xs))"
    "\<forall>\<rho>. rb (Comp M (cap xs)) \<rho> = rb (eval M (cap xs)) \<rho>" by blast+
  have "lam_WHN (rb M DVar) \<longleftrightarrow> lam_WHN (rb (eval M (cap xs)) DVar)"
    using Pure_rb[OF assms] ev(3) by simp
  also have "\<dots> \<longleftrightarrow> CFWHN (eval M (cap xs))" using SS_CFWHN_iff[OF ev(1)] .
  also have "\<dots> \<longleftrightarrow> CFWHN (Comp M (cap xs))"
  proof
    assume "CFWHN (eval M (cap xs))"
    then show "CFWHN (Comp M (cap xs))"
      using CFWHN_back_steps[OF sig_steps_wh[OF ev(2)]] by blast
  next
    assume "CFWHN (Comp M (cap xs))"
    then obtain N where r: "Comp M (cap xs) \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" and n: "WHNF N"
      by (auto simp: CFWHN_def)
    from steps_cd[OF r n] obtain k where "cd (Comp M (cap xs)) k N" by blast
    then have "cd (eval M (cap xs)) k N" using cd_sig_steps[OF ev(2)] by blast
    then have "lam_WHN (rb (eval M (cap xs)) DVar)" using cd_SS_lam_WHN ev(1) by blast
    then show "CFWHN (eval M (cap xs))" using SS_CFWHN_iff[OF ev(1)] by blast
  qed
  finally show ?thesis .
qed

theorem Pure_Relation:
  assumes "pure M" "fvp M \<subseteq> set xs"
  shows "(lam_WHN (rb M DVar) \<longleftrightarrow> CFWHN (Comp M (cap xs))) \<and>
         (CFWHN (Comp M (cap xs)) \<longleftrightarrow> CFWHSN (Comp M (cap xs))) \<and>
         (CFWHSN (Comp M (cap xs)) \<longleftrightarrow> Typ (Comp M (cap xs)))"
  using Pure_lam_CFWHN[OF assms] CFWHN_imp_CFWHSN_general CFWHSN_imp_CFWHN
    main_characterization main_characterization_full by blast

section \<open>The free-variable hypothesis is necessary\<close>

text \<open>
  \<open>M = (\<lambda>z. z) y\<close> with \<open>z = 1\<close>, \<open>y = 0\<close>, and \<open>xs = []\<close>: \<open>fvp M = {0} \<not>\<subseteq> set []\<close>.
\<close>

definition cex :: trm where "cex = App (Lam 1 (Var 1)) (Var 0)"

lemma cex_steps:
  "Comp cex (cap []) \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Comp (Var 0) Nil"
proof -
  have e: "cap [] = Nil" by (rule cap_Nil)
  have s1: "Comp cex Nil \<rightarrow>\<^sub>w\<^sub>h App (Comp (Lam 1 (Var 1)) Nil) (Comp (Var 0) Nil)"
    unfolding cex_def wh_def by (rule disjI1[OF sig.DApp])
  have s2: "App (Comp (Lam 1 (Var 1)) Nil) (Comp (Var 0) Nil)
      \<rightarrow>\<^sub>w\<^sub>h Comp (Var 1) (Extn (Comp (Var 0) Nil) 1 Nil)"
    unfolding wh_def by (rule disjI2[OF beta_h.Beta])
  have s3: "Comp (Var 1) (Extn (Comp (Var 0) Nil) 1 Nil) \<rightarrow>\<^sub>w\<^sub>h Comp (Var 0) Nil"
    unfolding wh_def by (rule disjI1[OF sig.VarRef])
  show ?thesis unfolding e
    using s1 s2 s3 by (meson r_into_rtranclp rtranclp_trans)
qed

lemma cex_not_CFWHN: "\<not> CFWHN (Comp cex (cap []))"
proof
  assume "CFWHN (Comp cex (cap []))"
  then obtain N where r: "Comp cex (cap []) \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" and n: "WHNF N" and nc: "\<not> clash N"
    by (auto simp: CFWHN_def)
  have c: "clash (Comp (Var 0) Nil)" by (rule CVarNil)
  from WHNF_unique[OF r n cex_steps clash_WHNF[OF c]] nc c show False by simp
qed

lemma Pure_FV_necessary:
  "pure cex \<and> \<not> (fvp cex \<subseteq> set ([] :: var list)) \<and>
   lam_WHN (rb cex DVar) \<and> \<not> CFWHN (Comp cex (cap [])) \<and>
   \<not> CFWHSN (Comp cex (cap [])) \<and> \<not> Typ (Comp cex (cap []))"
proof -
  have h: "DApp (DAbs (DVar 0)) (DVar 0) \<rightarrow>\<^sub>h DVar 0"
    using hbeta[of "DVar 0" "DVar 0"] by simp
  have "rb cex DVar = DApp (DAbs (DVar 0)) (DVar 0)" by (simp add: cex_def)
  then have "lam_WHN (rb cex DVar)"
    unfolding lam_WHN_def using h
    by (metis hneu.intros(1) hneu_normal r_into_rtranclp)
  then show ?thesis
    using cex_not_CFWHN CFWHSN_imp_CFWHN main_characterization
    by (auto simp: cex_def)
qed

end
