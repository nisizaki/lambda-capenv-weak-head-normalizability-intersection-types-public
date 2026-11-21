theory Typing
  imports Cap_Syntax
begin

section \<open>Intersection types with \<open>\<omega>\<close> and environment types (as in WH)\<close>

text \<open>
  \<open>Env m ob\<close>: \<open>m\<close> is an association list (first binding wins), \<open>ob = True\<close> is the
  open tail (essential), \<open>ob = False\<close> is the top tail (\<open>Env [] False\<close> plays the
  role of \<open>\<omega>\<close> as an environment).
\<close>

datatype ty =
    TV nat
  | Om
  | Arr ty ty
  | Inter ty ty
  | Env "(var \<times> ty) list" bool

definition emeet :: "(var \<times> ty) list \<Rightarrow> (var \<times> ty) list \<Rightarrow> (var \<times> ty) list" where
  "emeet m1 m2 =
     map (\<lambda>(x, A). (x, case map_of m2 x of Some B \<Rightarrow> Inter A B | None \<Rightarrow> A)) m1 @ m2"

lemma map_of_map_dep:
  "map_of (map (\<lambda>(x, A). (x, f x A)) m) y = map_option (f y) (map_of m y)"
  by (induction m) auto

lemma map_of_emeet:
  "map_of (emeet m1 m2) y =
     (case map_of m1 y of
        Some A \<Rightarrow> Some (case map_of m2 y of Some B \<Rightarrow> Inter A B | None \<Rightarrow> A)
      | None \<Rightarrow> map_of m2 y)"
  by (auto simp: emeet_def map_of_map_dep map_add_def split: option.split)

subsection \<open>Subtyping \<open>\<le>\<^sub>0\<close>\<close>

inductive sub :: "ty \<Rightarrow> ty \<Rightarrow> bool" (infix "\<preceq>" 50) where
  s_refl: "A \<preceq> A"
| s_trans: "A \<preceq> B \<Longrightarrow> B \<preceq> C \<Longrightarrow> A \<preceq> C"
| s_top: "A \<preceq> Om"
| s_il: "Inter A B \<preceq> A"
| s_ir: "Inter A B \<preceq> B"
| s_glb: "C \<preceq> A \<Longrightarrow> C \<preceq> B \<Longrightarrow> C \<preceq> Inter A B"
| s_arr: "A' \<preceq> A \<Longrightarrow> B \<preceq> B' \<Longrightarrow> Arr A B \<preceq> Arr A' B'"
| s_env: "(\<forall>x A'. map_of m' x = Some A' \<longrightarrow> (\<exists>A. map_of m x = Some A \<and> A \<preceq> A')) \<Longrightarrow>
          (ob' \<longrightarrow> ob) \<Longrightarrow> Env m ob \<preceq> Env m' ob'"
| s_emeet: "Inter (Env m1 o1) (Env m2 o2) \<preceq> Env (emeet m1 m2) (o1 \<or> o2)"
| s_omenv: "Om \<preceq> Env [] False"

fun ess :: "ty \<Rightarrow> bool" where
  "ess (TV n) = True"
| "ess Om = False"
| "ess (Arr A B) = True"
| "ess (Inter A B) = (ess A \<or> ess B)"
| "ess (Env m ob) = (m \<noteq> [] \<or> ob)"

lemma ess_down: "A \<preceq> B \<Longrightarrow> ess B \<Longrightarrow> ess A"
proof (induction rule: sub.induct)
  case (s_env m' m ob' ob)
  show ?case
  proof (cases "m' = []")
    case True
    then show ?thesis using s_env by auto
  next
    case False
    then obtain p ps where "m' = p # ps" by (cases m') auto
    then have "map_of m' (fst p) = Some (snd p)" by (cases p) simp
    then obtain x A' where "map_of m' x = Some A'" by blast
    with s_env.IH obtain A where "map_of m x = Some A" by blast
    then show ?thesis by auto
  qed
next
  case (s_emeet m1 o1 m2 o2)
  then show ?case by (auto simp: emeet_def)
qed auto

lemma sub_env_ext_meet1:
  "Env ((x, Inter B1 B2) # emeet m1 m2) (o1 \<or> o2) \<preceq> Env ((x, B1) # m1) o1"
proof (rule s_env)
  show "\<forall>y A'. map_of ((x, B1) # m1) y = Some A' \<longrightarrow>
         (\<exists>A. map_of ((x, Inter B1 B2) # emeet m1 m2) y = Some A \<and> A \<preceq> A')"
    by (auto simp: map_of_emeet intro: s_il s_refl split: option.split)
qed simp

lemma sub_env_ext_meet2:
  "Env ((x, Inter B1 B2) # emeet m1 m2) (o1 \<or> o2) \<preceq> Env ((x, B2) # m2) o2"
proof (rule s_env)
  show "\<forall>y A'. map_of ((x, B2) # m2) y = Some A' \<longrightarrow>
         (\<exists>A. map_of ((x, Inter B1 B2) # emeet m1 m2) y = Some A \<and> A \<preceq> A')"
    by (auto simp: map_of_emeet intro: s_ir s_refl split: option.split)
qed simp

subsection \<open>Contexts: environment contexts and top-level contexts (design F)\<close>

text \<open>
  \<open>CE C\<close> types \<open>M\<close> as evaluated in an environment of type \<open>C\<close>;
  \<open>CT m\<close> types \<open>M\<close> at top level (no environment), \<open>m\<close> giving the types of free
  variables.  \<open>Top\<close> is not a type, so \<open>\<omega> \<preceq> Env [] False\<close> cannot be used to fire
  \<open>TLam\<close> at top level.
\<close>

datatype ctx = CE ty | CT "(var \<times> ty) list"

definition fields_le :: "(var \<times> ty) list \<Rightarrow> (var \<times> ty) list \<Rightarrow> bool" where
  "fields_le m' m \<longleftrightarrow> (\<forall>x A. map_of m x = Some A \<longrightarrow> (\<exists>A'. map_of m' x = Some A' \<and> A' \<preceq> A))"

fun csub :: "ctx \<Rightarrow> ctx \<Rightarrow> bool" (infix "\<sqsubseteq>" 50) where
  "CE C' \<sqsubseteq> CE C \<longleftrightarrow> C' \<preceq> C"
| "CT m' \<sqsubseteq> CT m \<longleftrightarrow> fields_le m' m"
| "_ \<sqsubseteq> _ \<longleftrightarrow> False"

fun provides :: "ctx \<Rightarrow> (var \<times> ty) list \<Rightarrow> bool" where
  "provides (CE C) m \<longleftrightarrow> (\<exists>ob. C \<preceq> Env m ob)"
| "provides (CT m0) m \<longleftrightarrow> fields_le m0 m"

subsection \<open>Typing\<close>

inductive hasty :: "ctx \<Rightarrow> trm \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ : _" [51, 51, 51] 50) where
  TVar: "provides \<Gamma> m \<Longrightarrow> map_of m x = Some A \<Longrightarrow> \<Gamma> \<turnstile> Var x : A"
| TLam: "C \<preceq> Env m ob \<Longrightarrow> CE (Env ((x, A) # m) ob) \<turnstile> M : B \<Longrightarrow> CE C \<turnstile> Lam x M : Arr A B"
| TCode: "\<Gamma> \<turnstile> Lam x M : Arr Om Om"
| TNil: "\<Gamma> \<turnstile> Nil : Env [] True"
| TApp: "\<Gamma> \<turnstile> M : Arr A B \<Longrightarrow> \<Gamma> \<turnstile> N : A \<Longrightarrow> \<Gamma> \<turnstile> App M N : B"
| TExtn: "\<Gamma> \<turnstile> M : A \<Longrightarrow> \<Gamma> \<turnstile> N : Env m ob \<Longrightarrow> \<Gamma> \<turnstile> Extn M x N : Env ((x, A) # m) ob"
| TComp: "\<Gamma> \<turnstile> N : D \<Longrightarrow> CE D \<turnstile> M : A \<Longrightarrow> \<Gamma> \<turnstile> Comp M N : A"
| TOm: "\<Gamma> \<turnstile> M : Om"
| TInter: "\<Gamma> \<turnstile> M : A \<Longrightarrow> \<Gamma> \<turnstile> M : B \<Longrightarrow> \<Gamma> \<turnstile> M : Inter A B"
| TSub: "\<Gamma> \<turnstile> M : A \<Longrightarrow> A \<preceq> B \<Longrightarrow> \<Gamma> \<turnstile> M : B"

definition Typ :: "trm \<Rightarrow> bool" where
  "Typ M \<longleftrightarrow> (\<exists>m A. CT m \<turnstile> M : A \<and> ess A)"

subsection \<open>Basic lemmas\<close>

lemma csub_refl: "\<Gamma> \<sqsubseteq> \<Gamma>"
  by (cases \<Gamma>) (auto simp: fields_le_def intro: s_refl)

lemma provides_narrow: "provides \<Gamma> m \<Longrightarrow> \<Gamma>' \<sqsubseteq> \<Gamma> \<Longrightarrow> provides \<Gamma>' m"
proof (cases \<Gamma>; cases \<Gamma>')
  fix C C' assume a: "\<Gamma> = CE C" "\<Gamma>' = CE C'" "provides \<Gamma> m" "\<Gamma>' \<sqsubseteq> \<Gamma>"
  then obtain ob where "C \<preceq> Env m ob" "C' \<preceq> C" by auto
  then have "C' \<preceq> Env m ob" by (rule s_trans[rotated])
  then show "provides \<Gamma>' m" using a(2) by auto
next
  fix m0 m0' assume "\<Gamma> = CT m0" "\<Gamma>' = CT m0'" "provides \<Gamma> m" "\<Gamma>' \<sqsubseteq> \<Gamma>"
  then have f: "fields_le m0 m" "fields_le m0' m0" by simp_all
  have "fields_le m0' m"
    unfolding fields_le_def
  proof (intro allI impI)
    fix x A assume "map_of m x = Some A"
    then obtain B where "map_of m0 x = Some B" "B \<preceq> A" using f(1) unfolding fields_le_def by blast
    moreover obtain B' where "map_of m0' x = Some B'" "B' \<preceq> B"
      using f(2) \<open>map_of m0 x = Some B\<close> unfolding fields_le_def by blast
    ultimately show "\<exists>A'. map_of m0' x = Some A' \<and> A' \<preceq> A" by (blast intro: s_trans)
  qed
  then show "provides \<Gamma>' m" using \<open>\<Gamma>' = CT m0'\<close> by simp
qed auto

lemma narrowing: "\<Gamma> \<turnstile> M : A \<Longrightarrow> \<Gamma>' \<sqsubseteq> \<Gamma> \<Longrightarrow> \<Gamma>' \<turnstile> M : A"
proof (induction arbitrary: \<Gamma>' rule: hasty.induct)
  case (TVar \<Gamma> m x A)
  then show ?case by (blast intro: hasty.TVar provides_narrow)
next
  case (TLam C m ob x A M B)
  then obtain C' where c: "\<Gamma>' = CE C'" "C' \<preceq> C" by (cases \<Gamma>') auto
  from c(2) TLam.hyps(1) have "C' \<preceq> Env m ob" by (rule s_trans)
  then have "CE C' \<turnstile> Lam x M : Arr A B" using TLam.hyps(2) by (rule hasty.TLam)
  then show ?case using c(1) by simp
next
  case (TComp \<Gamma> N D M A)
  then show ?case by (blast intro: hasty.TComp)
qed (blast intro: hasty.intros)+

lemma typ_env_om: "\<Gamma> \<turnstile> M : Env [] False"
  by (rule TSub[OF TOm s_omenv])

lemma gen_Nil_aux: "\<Gamma> \<turnstile> P : A \<Longrightarrow> P = Nil \<Longrightarrow> Env [] True \<preceq> A"
proof (induction rule: hasty.induct)
  case (TNil \<Gamma>)
  show ?case by (rule s_refl)
next
  case (TOm \<Gamma> M)
  show ?case by (rule s_top)
next
  case (TInter \<Gamma> M A B)
  then show ?case by (metis s_glb)
next
  case (TSub \<Gamma> M A B)
  then show ?case by (metis s_trans)
qed simp_all

lemma gen_Nil: "\<Gamma> \<turnstile> Nil : A \<longleftrightarrow> Env [] True \<preceq> A"
  using gen_Nil_aux TNil TSub by blast

lemma gen_Comp_aux:
  "\<Gamma> \<turnstile> P : A \<Longrightarrow> P = Comp M L \<Longrightarrow> \<exists>D. \<Gamma> \<turnstile> L : D \<and> CE D \<turnstile> M : A"
proof (induction rule: hasty.induct)
  case (TComp \<Gamma> N D M' A)
  then show ?case by blast
next
  case (TOm \<Gamma> P)
  then show ?case by (blast intro: hasty.TOm)
next
  case (TInter \<Gamma> P A B)
  then obtain D1 D2 where 1: "\<Gamma> \<turnstile> L : D1" "CE D1 \<turnstile> M : A" and 2: "\<Gamma> \<turnstile> L : D2" "CE D2 \<turnstile> M : B"
    by blast
  have "\<Gamma> \<turnstile> L : Inter D1 D2" using 1 2 by (blast intro: hasty.TInter)
  moreover have "CE (Inter D1 D2) \<turnstile> M : Inter A B"
  proof (rule hasty.TInter)
    show "CE (Inter D1 D2) \<turnstile> M : A" using 1(2) by (rule narrowing) (simp add: s_il)
    show "CE (Inter D1 D2) \<turnstile> M : B" using 2(2) by (rule narrowing) (simp add: s_ir)
  qed
  ultimately show ?case by blast
next
  case (TSub \<Gamma> P A B)
  then show ?case by (blast intro: hasty.TSub)
qed auto

lemma gen_Comp:
  "\<Gamma> \<turnstile> Comp M L : A \<Longrightarrow> \<exists>D. \<Gamma> \<turnstile> L : D \<and> CE D \<turnstile> M : A"
  using gen_Comp_aux by blast

lemma gen_Extn_aux:
  "\<Gamma> \<turnstile> P : D \<Longrightarrow> P = Extn N x L \<Longrightarrow>
     \<exists>B m ob. \<Gamma> \<turnstile> N : B \<and> \<Gamma> \<turnstile> L : Env m ob \<and> Env ((x, B) # m) ob \<preceq> D"
proof (induction rule: hasty.induct)
  case (TExtn \<Gamma> M A N' m ob x')
  then show ?case by (blast intro: s_refl)
next
  case (TOm \<Gamma> P)
  have "Env [(x, Om)] False \<preceq> Om" by (rule s_top)
  then show ?case using hasty.TOm typ_env_om by blast
next
  case (TInter \<Gamma> P A B)
  then obtain B1 m1 o1 B2 m2 o2 where
    1: "\<Gamma> \<turnstile> N : B1" "\<Gamma> \<turnstile> L : Env m1 o1" "Env ((x, B1) # m1) o1 \<preceq> A" and
    2: "\<Gamma> \<turnstile> N : B2" "\<Gamma> \<turnstile> L : Env m2 o2" "Env ((x, B2) # m2) o2 \<preceq> B"
    by blast
  have "\<Gamma> \<turnstile> N : Inter B1 B2" using 1 2 by (blast intro: hasty.TInter)
  moreover have "\<Gamma> \<turnstile> L : Env (emeet m1 m2) (o1 \<or> o2)"
    using 1 2 by (blast intro: hasty.TInter hasty.TSub s_emeet)
  moreover have "Env ((x, Inter B1 B2) # emeet m1 m2) (o1 \<or> o2) \<preceq> Inter A B"
    using 1 2 by (blast intro: s_glb s_trans sub_env_ext_meet1 sub_env_ext_meet2)
  ultimately show ?case by blast
next
  case (TSub \<Gamma> P A B)
  then show ?case by (blast intro: s_trans)
qed auto

lemma gen_Extn:
  "\<Gamma> \<turnstile> Extn N x L : D \<Longrightarrow>
     \<exists>B m ob. \<Gamma> \<turnstile> N : B \<and> \<Gamma> \<turnstile> L : Env m ob \<and> Env ((x, B) # m) ob \<preceq> D"
  using gen_Extn_aux by blast

lemma provides_emeet:
  "provides \<Gamma> m1 \<Longrightarrow> provides \<Gamma> m2 \<Longrightarrow> provides \<Gamma> (emeet m1 m2)"
proof (cases \<Gamma>)
  case (CE C)
  assume "provides \<Gamma> m1" "provides \<Gamma> m2"
  then obtain o1 o2 where "C \<preceq> Env m1 o1" "C \<preceq> Env m2 o2" using CE by auto
  then have "C \<preceq> Inter (Env m1 o1) (Env m2 o2)" by (rule s_glb)
  then have "C \<preceq> Env (emeet m1 m2) (o1 \<or> o2)" using s_emeet by (rule s_trans)
  then show ?thesis using CE by auto
next
  case (CT m0)
  assume "provides \<Gamma> m1" "provides \<Gamma> m2"
  then have h1: "fields_le m0 m1" and h2: "fields_le m0 m2" using CT by simp_all
  have "fields_le m0 (emeet m1 m2)"
    unfolding fields_le_def
  proof (intro allI impI)
    fix y X assume "map_of (emeet m1 m2) y = Some X"
    then show "\<exists>A'. map_of m0 y = Some A' \<and> A' \<preceq> X"
    proof (cases "map_of m1 y")
      case None
      then have "map_of m2 y = Some X" using \<open>map_of (emeet m1 m2) y = Some X\<close>
        by (simp add: map_of_emeet)
      then show ?thesis using h2 unfolding fields_le_def by blast
    next
      case (Some A1)
      then obtain a1 where a1: "map_of m0 y = Some a1" "a1 \<preceq> A1"
        using h1 unfolding fields_le_def by blast
      show ?thesis
      proof (cases "map_of m2 y")
        case None
        then have "X = A1" using \<open>map_of (emeet m1 m2) y = Some X\<close> Some
          by (simp add: map_of_emeet)
        then show ?thesis using a1 by blast
      next
        case (Some A2)
        then have "X = Inter A1 A2" using \<open>map_of (emeet m1 m2) y = Some X\<close> \<open>map_of m1 y = Some A1\<close>
          by (simp add: map_of_emeet)
        moreover obtain a2 where "map_of m0 y = Some a2" "a2 \<preceq> A2"
          using h2 Some unfolding fields_le_def by blast
        ultimately show ?thesis using a1 by (metis option.inject s_glb s_trans s_il s_ir)
      qed
    qed
  qed
  then show ?thesis using CT by simp
qed

lemma gen_Var_aux:
  "\<Gamma> \<turnstile> P : A \<Longrightarrow> P = Var y \<Longrightarrow>
     Om \<preceq> A \<or> (\<exists>m B. provides \<Gamma> m \<and> map_of m y = Some B \<and> B \<preceq> A)"
proof (induction rule: hasty.induct)
  case (TVar \<Gamma> m x A)
  then show ?case by (blast intro: s_refl)
next
  case (TOm \<Gamma> P)
  then show ?case by (blast intro: s_refl)
next
  case (TInter \<Gamma> P A B)
  from TInter.IH TInter.prems consider
      (oo) "Om \<preceq> A" "Om \<preceq> B"
    | (oe) "Om \<preceq> A" "\<exists>m B'. provides \<Gamma> m \<and> map_of m y = Some B' \<and> B' \<preceq> B"
    | (eo) "\<exists>m B'. provides \<Gamma> m \<and> map_of m y = Some B' \<and> B' \<preceq> A" "Om \<preceq> B"
    | (ee) "\<exists>m B'. provides \<Gamma> m \<and> map_of m y = Some B' \<and> B' \<preceq> A"
           "\<exists>m B'. provides \<Gamma> m \<and> map_of m y = Some B' \<and> B' \<preceq> B"
    by blast
  then show ?case
  proof cases
    case oo
    then have "Om \<preceq> Inter A B" by (rule s_glb)
    then show ?thesis by blast
  next
    case oe
    then obtain m B' where p: "provides \<Gamma> m" and l: "map_of m y = Some B'" and h: "B' \<preceq> B" by blast
    have "B' \<preceq> Om" by (rule s_top)
    then have "B' \<preceq> A" using oe(1) by (rule s_trans)
    then have "B' \<preceq> Inter A B" using h by (rule s_glb)
    then show ?thesis using p l by blast
  next
    case eo
    then obtain m B' where p: "provides \<Gamma> m" and l: "map_of m y = Some B'" and h: "B' \<preceq> A" by blast
    have "B' \<preceq> Om" by (rule s_top)
    then have "B' \<preceq> B" using eo(2) by (rule s_trans)
    then have "B' \<preceq> Inter A B" using h by (rule s_glb[rotated])
    then show ?thesis using p l by blast
  next
    case ee
    then obtain m1 B1 m2 B2 where
      1: "provides \<Gamma> m1" "map_of m1 y = Some B1" "B1 \<preceq> A" and
      2: "provides \<Gamma> m2" "map_of m2 y = Some B2" "B2 \<preceq> B"
      by blast
    have "provides \<Gamma> (emeet m1 m2)" using 1(1) 2(1) by (rule provides_emeet)
    moreover have "map_of (emeet m1 m2) y = Some (Inter B1 B2)"
      using 1 2 by (simp add: map_of_emeet)
    moreover have "Inter B1 B2 \<preceq> Inter A B"
    proof (rule s_glb)
      show "Inter B1 B2 \<preceq> A" by (rule s_trans[OF s_il 1(3)])
      show "Inter B1 B2 \<preceq> B" by (rule s_trans[OF s_ir 2(3)])
    qed
    ultimately show ?thesis by blast
  qed
next
  case (TSub \<Gamma> P A B)
  then show ?case by (blast intro: s_trans)
qed auto

lemma gen_Var:
  "\<Gamma> \<turnstile> Var y : A \<Longrightarrow>
     Om \<preceq> A \<or> (\<exists>m B. provides \<Gamma> m \<and> map_of m y = Some B \<and> B \<preceq> A)"
  using gen_Var_aux by blast

lemma top_meet: "CT m1 \<turnstile> M : A \<Longrightarrow> CT m2 \<turnstile> M : B \<Longrightarrow> CT (emeet m1 m2) \<turnstile> M : Inter A B"
proof -
  assume h1: "CT m1 \<turnstile> M : A" and h2: "CT m2 \<turnstile> M : B"
  have f1: "CT (emeet m1 m2) \<sqsubseteq> CT m1" and f2: "CT (emeet m1 m2) \<sqsubseteq> CT m2"
    unfolding csub.simps fields_le_def
    by (auto simp: map_of_emeet split: option.split intro: s_il s_ir s_refl)
  show ?thesis
    by (rule hasty.TInter[OF narrowing[OF h1 f1] narrowing[OF h2 f2]])
qed

end
