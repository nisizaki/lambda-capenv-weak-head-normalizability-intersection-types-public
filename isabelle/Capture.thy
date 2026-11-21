theory Capture
  imports Uniform
begin

section \<open>Capture environments\<close>

text \<open>
  \<open>cap xs = (x\<^sub>1/x\<^sub>1)\<cdot>(\<dots>\<cdot>((x\<^sub>n/x\<^sub>n)\<cdot>()))\<close> (Cap_Syntax.thy).
  \<open>capE xs E\<close> is the result of pushing \<open>E\<close> into the fields:
  \<open>(x\<^sub>1\<circ>E)/x\<^sub>1\<cdot>(\<dots>\<cdot>((x\<^sub>n\<circ>E)/x\<^sub>n\<cdot>()))\<close>.
  The paper's \<open>y\<circ>()\<close> is \<open>Comp (Var y) Nil\<close>.
\<close>

lemma cap_Nil [simp]: "cap [] = Nil"
  by (simp add: cap_def)

lemma cap_Cons [simp]: "cap (x # xs) = Extn (Var x) x (cap xs)"
  by (simp add: cap_def)

definition capE :: "var list \<Rightarrow> trm \<Rightarrow> trm" where
  "capE xs E = foldr (\<lambda>x e. Extn (Comp (Var x) E) x e) xs Nil"

lemma capE_Nil [simp]: "capE [] E = Nil"
  by (simp add: capE_def)

lemma capE_Cons [simp]: "capE (x # xs) E = Extn (Comp (Var x) E) x (capE xs E)"
  by (simp add: capE_def)

subsection \<open>Proposition 10.1: typing of \<open>cap xs\<close>\<close>

theorem cap_typed:
  assumes "\<forall>(x, B) \<in> set ps. \<Gamma> \<turnstile> Var x : B"
  shows "\<Gamma> \<turnstile> cap (map fst ps) : Env ps True"
  using assms
proof (induction ps)
  case Nil
  show ?case by (simp add: TNil)
next
  case (Cons p ps)
  obtain x B where p: "p = (x, B)" by (cases p)
  have h: "\<Gamma> \<turnstile> Var x : B" using Cons.prems p by simp
  have t: "\<Gamma> \<turnstile> cap (map fst ps) : Env ps True"
    using Cons.IH Cons.prems by simp
  show ?case using TExtn[OF h t] p by simp
qed

theorem cap_typed_provides:
  assumes "provides \<Gamma> m" and "\<forall>x \<in> set xs. x \<in> dom (map_of m)"
  shows "\<Gamma> \<turnstile> cap xs : Env (map (\<lambda>x. (x, the (map_of m x))) xs) True"
proof -
  have eq: "map fst (map (\<lambda>x. (x, the (map_of m x))) xs) = xs"
    by (induction xs) simp_all
  have "\<Gamma> \<turnstile> cap (map fst (map (\<lambda>x. (x, the (map_of m x))) xs)) :
          Env (map (\<lambda>x. (x, the (map_of m x))) xs) True"
  proof (rule cap_typed, clarify)
    fix x B assume "(x, B) \<in> set (map (\<lambda>x. (x, the (map_of m x))) xs)"
    then have xs: "x \<in> set xs" and B: "B = the (map_of m x)" by auto
    from xs assms(2) have "x \<in> dom (map_of m)" by blast
    then have "map_of m x = Some B" using B by (auto simp: dom_def)
    then show "\<Gamma> \<turnstile> Var x : B" by (rule TVar[OF assms(1)])
  qed
  then show ?thesis using eq by simp
qed

subsection \<open>Proposition 10.2: reduction of \<open>(cap xs)\<circ>E\<close>\<close>

lemma ss_ExtnR: "sig\<^sup>*\<^sup>* M N \<Longrightarrow> sig\<^sup>*\<^sup>* (Extn L x M) (Extn L x N)"
  by (induction rule: rtranclp.induct) (auto intro: sig.ExtnR rtranclp.intros)

lemma ss_trans: "sig\<^sup>*\<^sup>* A B \<Longrightarrow> sig\<^sup>*\<^sup>* B C \<Longrightarrow> sig\<^sup>*\<^sup>* A C"
  by (rule rtranclp_trans)

theorem cap_comp_sigma: "sig\<^sup>*\<^sup>* (Comp (cap xs) E) (capE xs E)"
proof (induction xs)
  case Nil
  show ?case by (simp add: ss1[OF sig.DNil])
next
  case (Cons x xs)
  have "sig\<^sup>*\<^sup>* (Extn (Comp (Var x) E) x (Comp (cap xs) E)) (Extn (Comp (Var x) E) x (capE xs E))"
    by (rule ss_ExtnR[OF Cons.IH])
  moreover have "sig (Comp (Extn (Var x) x (cap xs)) E)
      (Extn (Comp (Var x) E) x (Comp (cap xs) E))" by (rule sig.DExtn)
  ultimately show ?case
    by (simp add: converse_rtranclp_into_rtranclp)
qed

lemma capE_hit:
  "y \<in> set xs \<Longrightarrow> sig\<^sup>*\<^sup>* (Comp (Var y) (capE xs E)) (Comp (Var y) E)"
proof (induction xs)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "x = y")
    case True
    then show ?thesis by (simp add: ss1[OF sig.VarRef])
  next
    case False
    then have ne: "x \<noteq> y" .
    with Cons.prems have "y \<in> set xs" by simp
    from converse_rtranclp_into_rtranclp[OF sig.VarSkip[OF ne] Cons.IH[OF this]]
    show ?thesis by simp
  qed
qed

lemma capE_miss:
  "y \<notin> set xs \<Longrightarrow> sig\<^sup>*\<^sup>* (Comp (Var y) (capE xs E)) (Comp (Var y) Nil)"
proof (induction xs)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  then have ne: "x \<noteq> y" and "y \<notin> set xs" by auto
  from converse_rtranclp_into_rtranclp[OF sig.VarSkip[OF ne] Cons.IH[OF this(2)]]
  show ?case by simp
qed

lemma cap_hit: "y \<in> set xs \<Longrightarrow> sig\<^sup>*\<^sup>* (Comp (Var y) (cap xs)) (Var y)"
proof (induction xs)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "x = y")
    case True
    then show ?thesis by (simp add: ss1[OF sig.VarRef])
  next
    case False
    then have ne: "x \<noteq> y" .
    with Cons.prems have "y \<in> set xs" by simp
    from converse_rtranclp_into_rtranclp[OF sig.VarSkip[OF ne] Cons.IH[OF this]]
    show ?thesis by simp
  qed
qed

lemma cap_miss: "y \<notin> set xs \<Longrightarrow> sig\<^sup>*\<^sup>* (Comp (Var y) (cap xs)) (Comp (Var y) Nil)"
proof (induction xs)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  then have ne: "x \<noteq> y" and "y \<notin> set xs" by auto
  from converse_rtranclp_into_rtranclp[OF sig.VarSkip[OF ne] Cons.IH[OF this(2)]]
  show ?case by simp
qed

theorem cap_captured:
  assumes "y \<in> set xs"
  shows "sig\<^sup>*\<^sup>* (Comp (Var y) (cap xs)) (Var y)"
    and "sig\<^sup>*\<^sup>* (Comp (Var y) (Comp (cap xs) E)) (Comp (Var y) E)"
proof -
  show "sig\<^sup>*\<^sup>* (Comp (Var y) (cap xs)) (Var y)" by (rule cap_hit[OF assms])
  show "sig\<^sup>*\<^sup>* (Comp (Var y) (Comp (cap xs) E)) (Comp (Var y) E)"
    by (rule ss_trans[OF ss_CompR[OF cap_comp_sigma] capE_hit[OF assms]])
qed

theorem cap_uncaptured:
  assumes "y \<notin> set xs"
  shows "sig\<^sup>*\<^sup>* (Comp (Var y) (cap xs)) (Comp (Var y) Nil)"
    and "sig\<^sup>*\<^sup>* (Comp (Var y) (Comp (cap xs) E)) (Comp (Var y) Nil)"
proof -
  show "sig\<^sup>*\<^sup>* (Comp (Var y) (cap xs)) (Comp (Var y) Nil)" by (rule cap_miss[OF assms])
  show "sig\<^sup>*\<^sup>* (Comp (Var y) (Comp (cap xs) E)) (Comp (Var y) Nil)"
    by (rule ss_trans[OF ss_CompR[OF cap_comp_sigma] capE_miss[OF assms]])
qed

subsection \<open>Clashes: unique reachable WHNF and the main theorem\<close>

lemma reach_clash_not_CFWHN:
  assumes "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" and "WHNF N" and "clash N"
  shows "\<not> CFWHN M"
proof
  assume "CFWHN M"
  then obtain N' where r: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N'" and n: "WHNF N'" and c: "\<not> clash N'"
    by (auto simp: CFWHN_def)
  from WHNF_unique[OF r n assms(1,2)] c assms(3) show False by simp
qed

lemma reach_clash_not_Typ:
  assumes "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" and "WHNF N" and "clash N"
  shows "\<not> Typ M"
  using reach_clash_not_CFWHN[OF assms] main_characterization by blast

lemma reach_clash_not_CFWHSN:
  assumes "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" and "WHNF N" and "clash N"
  shows "\<not> CFWHSN M"
  using reach_clash_not_CFWHN[OF assms] CFWHSN_imp_CFWHN by blast

lemma clash_y_Nil: "clash (Comp (Var y) Nil)"
  by (rule clash.CVarNil)

theorem cap_uncaptured_not_Typ:
  assumes "y \<notin> set xs"
  shows "\<not> Typ (Comp (Var y) (cap xs))"
proof (rule reach_clash_not_Typ)
  show "Comp (Var y) (cap xs) \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Comp (Var y) Nil"
    by (rule sig_steps_wh[OF cap_uncaptured(1)[OF assms]])
  show "WHNF (Comp (Var y) Nil)" by (rule clash_WHNF[OF clash_y_Nil])
  show "clash (Comp (Var y) Nil)" by (rule clash_y_Nil)
qed

theorem cap_uncaptured_not_CFWHN_CFWHSN:
  assumes "y \<notin> set xs"
  shows "\<not> CFWHN (Comp (Var y) (cap xs))" and "\<not> CFWHSN (Comp (Var y) (cap xs))"
proof -
  have r: "Comp (Var y) (cap xs) \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Comp (Var y) Nil"
    by (rule sig_steps_wh[OF cap_uncaptured(1)[OF assms]])
  show "\<not> CFWHN (Comp (Var y) (cap xs))"
    by (rule reach_clash_not_CFWHN[OF r clash_WHNF[OF clash_y_Nil] clash_y_Nil])
  show "\<not> CFWHSN (Comp (Var y) (cap xs))"
    by (rule reach_clash_not_CFWHSN[OF r clash_WHNF[OF clash_y_Nil] clash_y_Nil])
qed

theorem cap_comp_uncaptured_not_Typ:
  assumes "y \<notin> set xs"
  shows "\<not> Typ (Comp (Var y) (Comp (cap xs) E))"
proof (rule reach_clash_not_Typ)
  show "Comp (Var y) (Comp (cap xs) E) \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Comp (Var y) Nil"
    by (rule sig_steps_wh[OF cap_uncaptured(2)[OF assms]])
  show "WHNF (Comp (Var y) Nil)" by (rule clash_WHNF[OF clash_y_Nil])
  show "clash (Comp (Var y) Nil)" by (rule clash_y_Nil)
qed

subsection \<open>Captured variables reach a value\<close>

text \<open>
  In the notation of the paper: \<open>y\<circ>(cap xs) \<rightarrow>\<sigma>* y\<close> and \<open>y\<circ>((cap xs)\<circ>E) \<rightarrow>\<sigma>* y\<circ>E\<close>
  (\<open>cap_captured\<close>).  Note that \<open>y\<close> itself is neutral, not a \<open>val\<close>; the value is
  that of \<open>y\<circ>E\<close>, which the captured lookup now evaluates.
\<close>

theorem cap_captured_Typ:
  assumes "y \<in> set xs"
  shows "Typ (Comp (Var y) (cap xs))"
proof -
  have r: "Comp (Var y) (cap xs) \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Var y"
    by (rule sig_steps_wh[OF cap_captured(1)[OF assms]])
  have "Typ (Var y)" by (rule neu_Typ[OF neu.NVar])
  then show ?thesis unfolding Typ_def using subject_expansion_steps[OF r] by blast
qed

theorem cap_captured_reaches_value:
  assumes "y \<in> set xs" and "Comp (Var y) E \<rightarrow>\<^sub>w\<^sub>h\<^sup>* V" and "val V"
  shows "Comp (Var y) (Comp (cap xs) E) \<rightarrow>\<^sub>w\<^sub>h\<^sup>* V"
    and "Typ (Comp (Var y) (Comp (cap xs) E))"
proof -
  have r: "Comp (Var y) (Comp (cap xs) E) \<rightarrow>\<^sub>w\<^sub>h\<^sup>* V"
    by (rule rtranclp_trans[OF sig_steps_wh[OF cap_captured(2)[OF assms(1)]] assms(2)])
  show "Comp (Var y) (Comp (cap xs) E) \<rightarrow>\<^sub>w\<^sub>h\<^sup>* V" by (rule r)
  show "Typ (Comp (Var y) (Comp (cap xs) E))"
    using val_Typ[OF assms(3)] subject_expansion_steps[OF r] unfolding Typ_def by blast
qed

subsection \<open>Lemma 10.3 (\<open>gen_Cap\<close>) and Proposition 10.4 (locality)\<close>

text \<open>
  Inversion of \<open>\<preceq>\<close> on environment fields.  \<open>flds A y\<close> is the field of \<open>y\<close> exposed by
  \<open>A\<close> (intersections of environments meet their fields).
\<close>

fun flds :: "ty \<Rightarrow> var \<Rightarrow> ty option" where
  "flds (TV n) y = None"
| "flds Om y = None"
| "flds (Arr A B) y = None"
| "flds (Env m ob) y = map_of m y"
| "flds (Inter A B) y =
     (case flds A y of
        None \<Rightarrow> flds B y
      | Some A1 \<Rightarrow> Some (case flds B y of None \<Rightarrow> A1 | Some B1 \<Rightarrow> Inter A1 B1))"

lemma flds_sub:
  assumes "A \<preceq> B"
  shows "flds B y = Some A' \<Longrightarrow> \<exists>A''. flds A y = Some A'' \<and> A'' \<preceq> A'"
  using assms
proof (induction arbitrary: A' rule: sub.induct)
  case (s_refl A)
  then show ?case by (blast intro: sub.s_refl)
next
  case (s_trans A B C)
  from s_trans.IH(2)[OF s_trans.prems] obtain B' where b: "flds B y = Some B'" "B' \<preceq> A'" by blast
  from s_trans.IH(1)[OF b(1)] obtain A'' where a: "flds A y = Some A''" "A'' \<preceq> B'" by blast
  have "A'' \<preceq> A'" by (rule sub.s_trans[OF a(2) b(2)])
  with a(1) show ?case by blast
next
  case (s_top A)
  then show ?case by simp
next
  case (s_il A B)
  show ?case
  proof (cases "flds B y")
    case None
    with s_il show ?thesis by (auto intro: sub.s_refl)
  next
    case (Some B1)
    with s_il show ?thesis by (auto intro: sub.s_il)
  qed
next
  case (s_ir A B)
  show ?case
  proof (cases "flds A y")
    case None
    with s_ir show ?thesis by (auto intro: sub.s_refl)
  next
    case (Some A1)
    with s_ir show ?thesis by (auto intro: sub.s_ir)
  qed
next
  case (s_glb C A B)
  show ?case
  proof (cases "flds A y"; cases "flds B y")
    assume "flds A y = None" "flds B y = None"
    with s_glb.prems show ?thesis by simp
  next
    fix b assume a: "flds A y = None" and b: "flds B y = Some b"
    then have "A' = b" using s_glb.prems by simp
    with s_glb.IH(2)[OF b] show ?thesis by blast
  next
    fix a assume a: "flds A y = Some a" and b: "flds B y = None"
    then have "A' = a" using s_glb.prems by simp
    with s_glb.IH(1)[OF a] show ?thesis by blast
  next
    fix a b assume a: "flds A y = Some a" and b: "flds B y = Some b"
    then have A': "A' = Inter a b" using s_glb.prems by simp
    obtain c1 where c1: "flds C y = Some c1" "c1 \<preceq> a" using s_glb.IH(1)[OF a] by blast
    obtain c2 where c2: "flds C y = Some c2" "c2 \<preceq> b" using s_glb.IH(2)[OF b] by blast
    from c1(1) c2(1) have "c1 = c2" by simp
    then have "c1 \<preceq> Inter a b" using c1(2) c2(2) by (blast intro: sub.s_glb)
    with c1(1) A' show ?thesis by blast
  qed
next
  case (s_arr A' A B B')
  then show ?case by simp
next
  case (s_env m' m ob' ob)
  then show ?case by (simp, blast)
next
  case (s_emeet m1 o1 m2 o2)
  show ?case
    using s_emeet by (auto simp: map_of_emeet intro: sub.s_refl split: option.splits)
next
  case s_omenv
  then show ?case by simp
qed

lemma gen_Cap:
  "\<Gamma> \<turnstile> cap xs : D \<Longrightarrow>
     \<exists>Bs. map fst Bs = xs \<and> (\<forall>(x, B) \<in> set Bs. \<Gamma> \<turnstile> Var x : B) \<and> Env Bs True \<preceq> D"
proof (induction xs arbitrary: D)
  case Nil
  then have "Env [] True \<preceq> D" by (simp add: gen_Nil)
  then show ?case by (intro exI[of _ "[]"]) simp
next
  case (Cons x xs)
  from Cons.prems have "\<Gamma> \<turnstile> Extn (Var x) x (cap xs) : D" by simp
  then obtain B m ob where h1: "\<Gamma> \<turnstile> Var x : B" and h2: "\<Gamma> \<turnstile> cap xs : Env m ob"
    and h3: "Env ((x, B) # m) ob \<preceq> D"
    by (blast dest: gen_Extn)
  from Cons.IH[OF h2] obtain Bs where
    e: "map fst Bs = xs" and t: "\<forall>(x, B) \<in> set Bs. \<Gamma> \<turnstile> Var x : B" and s: "Env Bs True \<preceq> Env m ob"
    by blast
  have s2: "Env ((x, B) # Bs) True \<preceq> Env ((x, B) # m) ob"
  proof (rule s_env)
    show "\<forall>y A'. map_of ((x, B) # m) y = Some A' \<longrightarrow>
            (\<exists>A. map_of ((x, B) # Bs) y = Some A \<and> A \<preceq> A')"
    proof (intro allI impI)
      fix y A' assume l: "map_of ((x, B) # m) y = Some A'"
      show "\<exists>A. map_of ((x, B) # Bs) y = Some A \<and> A \<preceq> A'"
      proof (cases "y = x")
        case True
        with l show ?thesis by (auto intro: sub.s_refl)
      next
        case False
        with l have "map_of m y = Some A'" by simp
        from flds_sub[OF s, of y A'] this False show ?thesis by simp
      qed
    qed
  qed simp
  have s3: "Env ((x, B) # Bs) True \<preceq> D" by (rule sub.s_trans[OF s2 h3])
  show ?case
    apply (rule exI[of _ "(x, B) # Bs"])
    using e t h1 s3 by auto
qed

theorem cap_locality:
  "\<Gamma> \<turnstile> Comp M (cap xs) : A \<longleftrightarrow>
     (\<exists>Bs. map fst Bs = xs \<and> (\<forall>(x, B) \<in> set Bs. \<Gamma> \<turnstile> Var x : B) \<and>
           CE (Env Bs True) \<turnstile> M : A)"
proof
  assume "\<Gamma> \<turnstile> Comp M (cap xs) : A"
  then obtain D where d1: "\<Gamma> \<turnstile> cap xs : D" and d2: "CE D \<turnstile> M : A"
    by (blast dest: gen_Comp)
  from gen_Cap[OF d1] obtain Bs where
    e: "map fst Bs = xs" and t: "\<forall>(x, B) \<in> set Bs. \<Gamma> \<turnstile> Var x : B" and s: "Env Bs True \<preceq> D"
    by blast
  have "CE (Env Bs True) \<sqsubseteq> CE D" using s by simp
  from narrowing[OF d2 this] e t show "\<exists>Bs. map fst Bs = xs \<and> (\<forall>(x, B) \<in> set Bs. \<Gamma> \<turnstile> Var x : B) \<and>
           CE (Env Bs True) \<turnstile> M : A" by blast
next
  assume "\<exists>Bs. map fst Bs = xs \<and> (\<forall>(x, B) \<in> set Bs. \<Gamma> \<turnstile> Var x : B) \<and> CE (Env Bs True) \<turnstile> M : A"
  then obtain Bs where e: "map fst Bs = xs" and t: "\<forall>(x, B) \<in> set Bs. \<Gamma> \<turnstile> Var x : B"
    and m: "CE (Env Bs True) \<turnstile> M : A" by blast
  from cap_typed[OF t] e have "\<Gamma> \<turnstile> cap xs : Env Bs True" by simp
  from TComp[OF this m] show "\<Gamma> \<turnstile> Comp M (cap xs) : A" .
qed

corollary cap_nonretention:
  assumes "\<forall>x \<in> set xs. \<forall>B. \<Gamma> \<turnstile> Var x : B \<longleftrightarrow> \<Gamma>' \<turnstile> Var x : B"
  shows "\<Gamma> \<turnstile> Comp M (cap xs) : A \<longleftrightarrow> \<Gamma>' \<turnstile> Comp M (cap xs) : A"
proof -
  have "\<And>Bs. map fst Bs = xs \<Longrightarrow> (\<forall>(x, B) \<in> set Bs. \<Gamma> \<turnstile> Var x : B) \<longleftrightarrow>
                                     (\<forall>(x, B) \<in> set Bs. \<Gamma>' \<turnstile> Var x : B)"
    using assms by force
  then show ?thesis unfolding cap_locality by blast
qed

lemma CT_Var_iff:
  "CT m \<turnstile> Var x : B \<longleftrightarrow> Om \<preceq> B \<or> (\<exists>A'. map_of m x = Some A' \<and> A' \<preceq> B)"
proof
  assume "CT m \<turnstile> Var x : B"
  from gen_Var[OF this] show "Om \<preceq> B \<or> (\<exists>A'. map_of m x = Some A' \<and> A' \<preceq> B)"
  proof
    assume "Om \<preceq> B" then show ?thesis by blast
  next
    assume "\<exists>m' B'. provides (CT m) m' \<and> map_of m' x = Some B' \<and> B' \<preceq> B"
    then obtain m' B' where p: "fields_le m m'" and l: "map_of m' x = Some B'" and b: "B' \<preceq> B"
      by auto
    from p l obtain A' where "map_of m x = Some A'" "A' \<preceq> B'" unfolding fields_le_def by blast
    then show ?thesis using b by (blast intro: sub.s_trans)
  qed
next
  assume "Om \<preceq> B \<or> (\<exists>A'. map_of m x = Some A' \<and> A' \<preceq> B)"
  then show "CT m \<turnstile> Var x : B"
  proof
    assume "Om \<preceq> B"
    from TSub[OF TOm this] show ?thesis .
  next
    assume "\<exists>A'. map_of m x = Some A' \<and> A' \<preceq> B"
    then obtain A' where l: "map_of m x = Some A'" and b: "A' \<preceq> B" by blast
    have p: "provides (CT m) m" by (simp add: fields_le_def sub.s_refl)
    from TSub[OF TVar[OF p l] b] show ?thesis .
  qed
qed

theorem cap_locality_top:
  "CT m \<turnstile> Comp M (cap xs) : A \<longleftrightarrow>
     (\<exists>Bs. map fst Bs = xs \<and>
           (\<forall>(x, B) \<in> set Bs. Om \<preceq> B \<or> (\<exists>A'. map_of m x = Some A' \<and> A' \<preceq> B)) \<and>
           CE (Env Bs True) \<turnstile> M : A)"
proof -
  have "\<And>Bs. (\<forall>(x, B) \<in> set Bs. CT m \<turnstile> Var x : B) \<longleftrightarrow>
        (\<forall>(x, B) \<in> set Bs. Om \<preceq> B \<or> (\<exists>A'. map_of m x = Some A' \<and> A' \<preceq> B))"
    by (auto simp: CT_Var_iff)
  then show ?thesis unfolding cap_locality by blast
qed

end
