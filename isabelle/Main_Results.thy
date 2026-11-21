theory Main_Results
  imports Completeness Soundness
begin

section \<open>Main results\<close>

theorem main_characterization: "Typ M \<longleftrightarrow> CFWHN M"
  using soundness completeness by blast

corollary clash_not_Typ: "WHNF M \<Longrightarrow> clash M \<Longrightarrow> \<not> Typ M"
proof
  assume n: "WHNF M" and c: "clash M" and "Typ M"
  then obtain N where r: "M \<rightarrow>\<^sub>w\<^sub>h\<^sup>* N" and nc: "\<not> clash N"
    using soundness by (auto simp: CFWHN_def)
  from normal_rtranclp[OF n r] nc c show False by simp
qed

end
