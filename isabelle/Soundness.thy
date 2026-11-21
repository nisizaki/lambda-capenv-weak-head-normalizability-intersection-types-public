theory Soundness
  imports Typing WHNF_Classes
begin

section \<open>Soundness: \<open>Typ M \<Longrightarrow> CFWHN M\<close>\<close>

text \<open>
  Realizability as in WH.  The basic lemma has two forms: in an environment
  context \<open>CE C\<close> it speaks about \<open>M \<circ> e\<close>, at top level \<open>CT m\<close> about \<open>M\<close> itself.
\<close>

subsection \<open>Auxiliary reduction lemmas\<close>

lemma CFWHN_back: "M \<rightarrow>\<^sub>w\<^sub>h M' \<Longrightarrow> CFWHN M' \<Longrightarrow> CFWHN M"
  unfolding CFWHN_def by (meson converse_rtranclp_into_rtranclp)

lemma CFWHN_back_steps: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* M' \<Longrightarrow> CFWHN M' \<Longrightarrow> CFWHN M"
  by (induction rule: converse_rtranclp_induct) (auto intro: CFWHN_back)

lemma sig_steps_wh: "sig\<^sup>*\<^sup>* M N \<Longrightarrow> M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl sig_imp_wh)

lemma sig_nf: "\<exists>N. sig\<^sup>*\<^sup>* M N \<and> sig_normal N"
proof -
  have "SN_at sig M" by (rule sig_SN)
  then show ?thesis
  proof (induction rule: SN_at_induct)
    case (step a)
    show ?case
    proof (cases "sig_normal a")
      case True then show ?thesis by blast
    next
      case False
      then obtain b where "a \<rightarrow>\<^sub>\<sigma> b" by (auto simp: normal_def)
      with step.IH[OF this] show ?thesis by (meson converse_rtranclp_into_rtranclp)
    qed
  qed
qed

lemma steps_lift:
  assumes "\<And>P Q. R P Q \<Longrightarrow> R' (f P) (f Q)"
  shows "R\<^sup>*\<^sup>* M N \<Longrightarrow> R'\<^sup>*\<^sup>* (f M) (f N)"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl assms)

lemma wh_steps_AppL: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* M' \<Longrightarrow> App M N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* App M' N"
  by (rule steps_lift[of wh wh "\<lambda>P. App P N"]) (auto intro: wh_AppL)

lemma sig_steps_AppR: "sig\<^sup>*\<^sup>* N N' \<Longrightarrow> App M N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* App M N'"
  by (rule steps_lift[of sig wh "\<lambda>P. App M P"]) (auto intro: sig_imp_wh sig.AppR)

lemma sig_steps_Lam: "sig\<^sup>*\<^sup>* M M' \<Longrightarrow> Lam x M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Lam x M'"
  by (rule steps_lift[of sig wh "\<lambda>P. Lam x P"]) (auto intro: sig_imp_wh sig.Lam)

lemma sig_steps_CompL: "sig\<^sup>*\<^sup>* M M' \<Longrightarrow> Comp M N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Comp M' N"
  by (rule steps_lift[of sig wh "\<lambda>P. Comp P N"]) (auto intro: sig_imp_wh sig.CompL)

lemma sig_steps_CompR: "sig\<^sup>*\<^sup>* N N' \<Longrightarrow> Comp M N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Comp M N'"
  by (rule steps_lift[of sig wh "\<lambda>P. Comp M P"]) (auto intro: sig_imp_wh sig.CompR)

lemma sig_steps_ExtnL: "sig\<^sup>*\<^sup>* M M' \<Longrightarrow> Extn M x N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Extn M' x N"
  by (rule steps_lift[of sig wh "\<lambda>P. Extn P x N"]) (auto intro: sig_imp_wh sig.ExtnL)

lemma sig_steps_ExtnR: "sig\<^sup>*\<^sup>* N N' \<Longrightarrow> Extn M x N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Extn M x N'"
  by (rule steps_lift[of sig wh "\<lambda>P. Extn M x P"]) (auto intro: sig_imp_wh sig.ExtnR)

lemma wh_steps_VarR: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* M' \<Longrightarrow> Comp (Var x) M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Comp (Var x) M'"
  by (rule steps_lift[of wh wh "\<lambda>P. Comp (Var x) P"]) (auto intro: wh_VarR)

lemma val_WHNF: "val M \<Longrightarrow> WHNF M"
  using WHNF_iff_classes val_not_clash by blast

lemma neu_WHNF: "neu M \<Longrightarrow> WHNF M"
  using WHNF_iff_classes neu_not_clash by blast

lemma val_CFWHN: "val M \<Longrightarrow> CFWHN M"
  unfolding CFWHN_def using val_WHNF val_not_clash by blast

lemma neu_CFWHN: "neu M \<Longrightarrow> CFWHN M"
  unfolding CFWHN_def using neu_WHNF neu_not_clash by blast

lemma CFWHN_Nil: "CFWHN Nil"
  by (rule val_CFWHN[OF VNil])

lemma CFWHN_Lam: "CFWHN (Lam x M)"
proof -
  obtain M' where s: "sig\<^sup>*\<^sup>* M M'" and n: "sig_normal M'" using sig_nf by blast
  have "val (Lam x M')" using n by (rule VLam)
  then show ?thesis using CFWHN_back_steps[OF sig_steps_Lam[OF s]] val_CFWHN by blast
qed

lemma CFWHN_Extn: "CFWHN (Extn M x N)"
proof -
  obtain M' where s1: "sig\<^sup>*\<^sup>* M M'" and n1: "sig_normal M'" using sig_nf by blast
  obtain N' where s2: "sig\<^sup>*\<^sup>* N N'" and n2: "sig_normal N'" using sig_nf by blast
  have r: "Extn M x N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Extn M' x N'"
    using sig_steps_ExtnL[OF s1] sig_steps_ExtnR[OF s2] by (rule rtranclp_trans)
  have "val (Extn M' x N')" using n1 n2 by (rule VExtn)
  then show ?thesis using CFWHN_back_steps[OF r] val_CFWHN by blast
qed

lemma CFWHN_Clo: "CFWHN (Comp (Lam x M) e)"
proof -
  obtain M' where s1: "sig\<^sup>*\<^sup>* M M'" and n1: "sig_normal M'" using sig_nf by blast
  obtain e' where s2: "sig\<^sup>*\<^sup>* e e'" and n2: "sig_normal e'" using sig_nf by blast
  have r: "Comp (Lam x M) e \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Comp (Lam x M') e'"
  proof -
    have "sig\<^sup>*\<^sup>* (Lam x M) (Lam x M')"
      by (rule steps_lift[of sig sig "\<lambda>P. Lam x P", OF sig.Lam s1])
    then have "Comp (Lam x M) e \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Comp (Lam x M') e" by (rule sig_steps_CompL)
    then show ?thesis using sig_steps_CompR[OF s2] by (rule rtranclp_trans)
  qed
  have "val (Comp (Lam x M') e')" using n1 n2 by (rule VClo)
  then show ?thesis using CFWHN_back_steps[OF r] val_CFWHN by blast
qed

text \<open>Weak neutral terms: arguments need not be \<open>\<sigma>\<close>-normal.\<close>

inductive wneu :: "trm \<Rightarrow> bool" where
  "wneu (Var x)"
| "wneu M \<Longrightarrow> wneu (App M N)"
| "wneu M \<Longrightarrow> wneu (Comp (Var x) M)"

lemma wneu_reduces: "wneu M \<Longrightarrow> \<exists>M'. M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* M' \<and> neu M'"
proof (induction rule: wneu.induct)
  case (1 x)
  then show ?case by (blast intro: neu.intros)
next
  case (2 M N)
  then obtain M' where r: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* M'" and n: "neu M'" by blast
  obtain N' where s: "sig\<^sup>*\<^sup>* N N'" and nn: "sig_normal N'" using sig_nf by blast
  have "App M N \<rightarrow>\<^sub>w\<^sub>h\<^sup>* App M' N'"
    using wh_steps_AppL[OF r] sig_steps_AppR[OF s] by (rule rtranclp_trans)
  moreover have "neu (App M' N')" using n nn by (rule NApp)
  ultimately show ?case by blast
next
  case (3 M x)
  then obtain M' where r: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* M'" and n: "neu M'" by blast
  have "Comp (Var x) M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* Comp (Var x) M'" by (rule wh_steps_VarR[OF r])
  moreover have "neu (Comp (Var x) M')" using n by (rule NComp)
  ultimately show ?case by blast
qed

lemma wneu_CFWHN: "wneu M \<Longrightarrow> CFWHN M"
  using wneu_reduces neu_CFWHN CFWHN_back_steps by blast

subsection \<open>Interpretation of types\<close>

fun I :: "ty \<Rightarrow> trm set" where
  "I (TV n) = {M. CFWHN M}"
| "I Om = UNIV"
| "I (Arr A B) = {M. CFWHN M \<and> (\<forall>N \<in> I A. App M N \<in> I B)}"
| "I (Inter A B) = I A \<inter> I B"
| "I (Env m ob) =
     {e. ((m \<noteq> [] \<or> ob) \<longrightarrow> CFWHN e) \<and>
         (\<forall>x S. map_of (map (\<lambda>(y, A). (y, I A)) m) x = Some S \<longrightarrow> Comp (Var x) e \<in> S)}"


lemma I_Env:
  "e \<in> I (Env m ob) \<longleftrightarrow>
     ((m \<noteq> [] \<or> ob) \<longrightarrow> CFWHN e) \<and> (\<forall>x A. map_of m x = Some A \<longrightarrow> Comp (Var x) e \<in> I A)"
  by (simp add: map_of_map_dep) blast

declare I.simps(5) [simp del]

lemma I_back: "M \<rightarrow>\<^sub>w\<^sub>h M' \<Longrightarrow> M' \<in> I A \<Longrightarrow> M \<in> I A"
proof (induction A arbitrary: M M')
  case (TV n) then show ?case using CFWHN_back by simp
next
  case Om then show ?case by simp
next
  case (Arr A B)
  then show ?case using CFWHN_back wh_AppL by simp blast
next
  case (Inter A B) then show ?case by simp
next
  case (Env m ob)
  have "Comp (Var x) M \<in> I A" if l: "map_of m x = Some A" for x A
  proof -
    have xa: "(x, A) \<in> set m" using l by (rule map_of_SomeD)
    have sn: "A \<in> Basic_BNFs.snds (x, A)" by simp
    have c: "Comp (Var x) M' \<in> I A" using Env.prems(2) l by (simp add: I_Env)
    show ?thesis by (rule Env.IH[OF xa sn wh_VarR[OF Env.prems(1)] c])
  qed
  then show ?case using Env.prems CFWHN_back by (simp add: I_Env)
qed

lemma I_ess: "ess A \<Longrightarrow> M \<in> I A \<Longrightarrow> CFWHN M"
proof (induction A arbitrary: M)
  case (TV n) then show ?case by simp
next
  case Om then show ?case by simp
next
  case (Arr A B) then show ?case by simp
next
  case (Inter A B)
  then show ?case by (cases "ess A") simp_all
next
  case (Env m ob)
  then show ?case by (simp add: I_Env)
qed

lemma wneu_I: "wneu M \<Longrightarrow> M \<in> I A"
proof (induction A arbitrary: M)
  case (TV n) then show ?case using wneu_CFWHN by simp
next
  case Om then show ?case by simp
next
  case (Arr A B)
  then show ?case using wneu_CFWHN wneu.intros(2) by simp
next
  case (Inter A B) then show ?case by simp
next
  case (Env m ob)
  have "Comp (Var x) M \<in> I A" if l: "map_of m x = Some A" for x A
  proof -
    have xa: "(x, A) \<in> set m" using l by (rule map_of_SomeD)
    have sn: "A \<in> Basic_BNFs.snds (x, A)" by simp
    have w: "wneu (Comp (Var x) M)" using Env.prems by (rule wneu.intros(3))
    show ?thesis by (rule Env.IH[OF xa sn w])
  qed
  then show ?case using Env.prems wneu_CFWHN by (simp add: I_Env)
qed

lemma Var_I: "Var x \<in> I A"
  by (rule wneu_I) (rule wneu.intros(1))

lemma I_mono: "A \<preceq> B \<Longrightarrow> I A \<subseteq> I B"
proof (induction rule: sub.induct)
  case (s_arr A' A B B')
  then show ?case by auto
next
  case (s_env m' m ob' ob)
  show ?case
  proof
    fix e
    assume e: "e \<in> I (Env m ob)"
    have cf: "CFWHN e" if "m' \<noteq> [] \<or> ob'"
    proof -
      have "m \<noteq> [] \<or> ob"
      proof (cases "m' = []")
        case True then show ?thesis using that s_env.hyps by auto
      next
        case False
        then obtain p ps where "m' = p # ps" by (cases m') auto
        then have "map_of m' (fst p) = Some (snd p)" by (cases p) simp
        then obtain A where "map_of m (fst p) = Some A" using s_env.IH by blast
        then show ?thesis by auto
      qed
      then show ?thesis using e by (simp add: I_Env)
    qed
    moreover have "Comp (Var x) e \<in> I A'" if l: "map_of m' x = Some A'" for x A'
    proof -
      obtain A where "map_of m x = Some A" and "I A \<subseteq> I A'"
        using s_env.IH l by blast
      then show ?thesis using e by (auto simp: I_Env)
    qed
    ultimately show "e \<in> I (Env m' ob')" by (simp add: I_Env)
  qed
next
  case (s_emeet m1 o1 m2 o2)
  show ?case
  proof
    fix e
    assume "e \<in> I (Inter (Env m1 o1) (Env m2 o2))"
    then have e1: "e \<in> I (Env m1 o1)" and e2: "e \<in> I (Env m2 o2)" by simp_all
    have cf: "CFWHN e" if "emeet m1 m2 \<noteq> [] \<or> o1 \<or> o2"
      using that e1 e2 by (auto simp: I_Env emeet_def)
    moreover have "Comp (Var x) e \<in> I A" if l: "map_of (emeet m1 m2) x = Some A" for x A
    proof (cases "map_of m1 x")
      case None
      then have "map_of m2 x = Some A" using l by (simp add: map_of_emeet)
      then show ?thesis using e2 by (simp add: I_Env)
    next
      case (Some A1)
      show ?thesis
      proof (cases "map_of m2 x")
        case None
        then have "A = A1" using l Some by (simp add: map_of_emeet)
        then show ?thesis using e1 Some by (simp add: I_Env)
      next
        case (Some A2)
        then have "A = Inter A1 A2" using l \<open>map_of m1 x = Some A1\<close> by (simp add: map_of_emeet)
        then show ?thesis using e1 e2 Some \<open>map_of m1 x = Some A1\<close> by (simp add: I_Env)
      qed
    qed
    ultimately show "e \<in> I (Env (emeet m1 m2) (o1 \<or> o2))" by (simp add: I_Env)
  qed
next
  case s_omenv
  then show ?case by (auto simp: I_Env)
qed auto

subsection \<open>Realizers\<close>

lemma Extn_I:
  assumes n: "N \<in> I A" and e: "e \<in> I (Env m ob)"
  shows "Extn N x e \<in> I (Env ((x, A) # m) ob)"
proof -
  have "Comp (Var y) (Extn N x e) \<in> I B" if l: "map_of ((x, A) # m) y = Some B" for y B
  proof (cases "y = x")
    case True
    then have "B = A" using l by simp
    then show ?thesis using True I_back[OF sig_imp_wh[OF sig.VarRef] n] by simp
  next
    case False
    then have "map_of m y = Some B" using l by simp
    then have "Comp (Var y) e \<in> I B" using e by (simp add: I_Env)
    moreover have "Comp (Var y) (Extn N x e) \<rightarrow>\<^sub>w\<^sub>h Comp (Var y) e"
      using False by (simp add: sig_imp_wh sig.VarSkip)
    ultimately show ?thesis using I_back by blast
  qed
  then show ?thesis using CFWHN_Extn by (simp add: I_Env)
qed

lemma Nil_I: "Nil \<in> I (Env [] True)"
  by (simp add: I_Env CFWHN_Nil)

subsection \<open>Basic lemma\<close>

lemma basic:
  "\<Gamma> \<turnstile> M : A \<Longrightarrow>
     (case \<Gamma> of CE C \<Rightarrow> (\<forall>e \<in> I C. Comp M e \<in> I A) | CT m \<Rightarrow> M \<in> I A)"
proof (induction rule: hasty.induct)
  case (TVar \<Gamma> m x A)
  show ?case
  proof (cases \<Gamma>)
    case (CE C)
    show ?thesis
    proof (clarsimp simp: CE)
      fix e assume e: "e \<in> I C"
      from TVar.hyps(1) obtain ob where "C \<preceq> Env m ob" using CE by auto
      then have "e \<in> I (Env m ob)" using I_mono e by blast
      then show "Comp (Var x) e \<in> I A" using TVar.hyps(2) by (simp add: I_Env)
    qed
  next
    case (CT m0) then show ?thesis by (simp add: Var_I)
  qed
next
  case (TLam C m ob x A M B)
  have key: "\<forall>e \<in> I C. Comp (Lam x M) e \<in> I (Arr A B)"
  proof
    fix e assume e: "e \<in> I C"
    have em: "e \<in> I (Env m ob)" using I_mono[OF TLam.hyps(1)] e by blast
    have app: "\<forall>N \<in> I A. App (Comp (Lam x M) e) N \<in> I B"
    proof
      fix N assume n: "N \<in> I A"
      have "Extn N x e \<in> I (Env ((x, A) # m) ob)" by (rule Extn_I[OF n em])
      then have "Comp M (Extn N x e) \<in> I B" using TLam.IH by force
      then show "App (Comp (Lam x M) e) N \<in> I B"
        by (rule I_back[OF beta_h_imp_wh[OF beta_h.Beta]])
    qed
    show "Comp (Lam x M) e \<in> I (Arr A B)" using app CFWHN_Clo by simp
  qed
  then show ?case by simp
next
  case (TCode \<Gamma> x M)
  show ?case
  proof (cases \<Gamma>)
    case (CE C) then show ?thesis by (simp add: CFWHN_Clo)
  next
    case (CT m) then show ?thesis by (simp add: CFWHN_Lam)
  qed
next
  case (TNil \<Gamma>)
  show ?case
  proof (cases \<Gamma>)
    case (CE C)
    show ?thesis
      using I_back[OF sig_imp_wh[OF sig.DNil] Nil_I] by (simp add: CE)
  next
    case (CT m) then show ?thesis using Nil_I by simp
  qed
next
  case (TApp \<Gamma> M A B N)
  show ?case
  proof (cases \<Gamma>)
    case (CE C)
    show ?thesis
    proof (clarsimp simp: CE)
      fix e assume e: "e \<in> I C"
      then have "Comp M e \<in> I (Arr A B)" "Comp N e \<in> I A" using TApp.IH CE by auto
      then have "App (Comp M e) (Comp N e) \<in> I B" by simp
      then show "Comp (App M N) e \<in> I B" using I_back[OF sig_imp_wh[OF sig.DApp]] by blast
    qed
  next
    case (CT m) then show ?thesis using TApp.IH by simp
  qed
next
  case (TExtn \<Gamma> M A N m ob x)
  show ?case
  proof (cases \<Gamma>)
    case (CE C)
    show ?thesis
    proof (clarsimp simp: CE)
      fix e assume e: "e \<in> I C"
      then have "Comp M e \<in> I A" "Comp N e \<in> I (Env m ob)" using TExtn.IH CE by auto
      then have "Extn (Comp M e) x (Comp N e) \<in> I (Env ((x, A) # m) ob)" by (rule Extn_I)
      then show "Comp (Extn M x N) e \<in> I (Env ((x, A) # m) ob)"
        using I_back[OF sig_imp_wh[OF sig.DExtn]] by blast
    qed
  next
    case (CT m0)
    then have "M \<in> I A" "N \<in> I (Env m ob)" using TExtn.IH by auto
    then show ?thesis using CT by (simp add: Extn_I)
  qed
next
  case (TComp \<Gamma> N D M A)
  show ?case
  proof (cases \<Gamma>)
    case (CE C)
    show ?thesis
    proof (clarsimp simp: CE)
      fix e assume e: "e \<in> I C"
      have n: "Comp N e \<in> I D" using TComp.IH(1) e CE by auto
      have "Comp M (Comp N e) \<in> I A" using TComp.IH(2) n by auto
      then show "Comp (Comp M N) e \<in> I A" using I_back[OF sig_imp_wh[OF sig.Ass]] by blast
    qed
  next
    case (CT m)
    then have n: "N \<in> I D" using TComp.IH(1) by simp
    then show ?thesis using TComp.IH(2) CT by auto
  qed
next
  case (TOm \<Gamma> M)
  show ?case by (cases \<Gamma>) simp_all
next
  case (TInter \<Gamma> M A B)
  show ?case
  proof (cases \<Gamma>)
    case (CE C)
    then show ?thesis using TInter.IH by simp
  next
    case (CT m)
    then show ?thesis using TInter.IH by simp
  qed
next
  case (TSub \<Gamma> M A B)
  show ?case
  proof (cases \<Gamma>)
    case (CE C)
    show ?thesis
    proof (clarsimp simp: CE)
      fix e assume e: "e \<in> I C"
      have "Comp M e \<in> I A" using TSub.IH e CE by simp
      then show "Comp M e \<in> I B" using I_mono[OF TSub.hyps(2)] by blast
    qed
  next
    case (CT m)
    then have "M \<in> I A" using TSub.IH by simp
    then show ?thesis using CT I_mono[OF TSub.hyps(2)] by auto
  qed
qed

theorem soundness: "Typ M \<Longrightarrow> CFWHN M"
proof -
  assume "Typ M"
  then obtain m A where t: "CT m \<turnstile> M : A" and e: "ess A" by (auto simp: Typ_def)
  have "M \<in> I A" using basic[OF t] by simp
  then show "CFWHN M" by (rule I_ess[OF e])
qed

end
