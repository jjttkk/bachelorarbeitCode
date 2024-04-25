section\<open>Preservation results for $\kappa$-closed forcing notions\<close>

theory Kappa_Closed_Notions
  imports
    Not_CH
begin

definition
  lerel :: "i\<Rightarrow>i" where
  "lerel(\<alpha>) \<equiv> Memrel(\<alpha>) \<union> id(\<alpha>)"

lemma lerelI[intro!]: "x\<le>y \<Longrightarrow> y\<in>\<alpha> \<Longrightarrow> Ord(\<alpha>) \<Longrightarrow> \<langle>x,y\<rangle> \<in> lerel(\<alpha>)"
  using Ord_trans[of x y \<alpha>] ltD unfolding lerel_def by auto

lemma lerelD[dest]: "\<langle>x,y\<rangle> \<in> lerel(\<alpha>) \<Longrightarrow> Ord(\<alpha>) \<Longrightarrow> x\<le>y"
  using ltI[THEN leI] Ord_in_Ord unfolding lerel_def by auto

definition
  mono_seqspace :: "[i,i,i] \<Rightarrow> i" (\<open>_ \<^sub><\<rightarrow> '(_,_')\<close> [61] 60) where
  "\<alpha> \<^sub><\<rightarrow> (P,leq) \<equiv> mono_map(\<alpha>,Memrel(\<alpha>),P,leq)"

relativize functional "mono_seqspace" "mono_seqspace_rel"
relationalize "mono_seqspace_rel" "is_mono_seqspace"
synthesize "is_mono_seqspace" from_definition assuming "nonempty"

context M_ZF_library
begin

rel_closed for "mono_seqspace"
  unfolding mono_seqspace_rel_def mono_map_rel_def
  using separation_closed separation_ball separation_imp separation_in
    lam_replacement_fst lam_replacement_snd lam_replacement_hcomp lam_replacement_constant
    lam_replacement_product
    lam_replacement_apply2[THEN[5] lam_replacement_hcomp2]
  by simp_all

end \<comment> \<open>\<^locale>\<open>M_ZF_library\<close>\<close>

abbreviation
  mono_seqspace_r (\<open>_ \<^sub><\<rightarrow>\<^bsup>_\<^esup> '(_,_')\<close> [61] 60) where
  "\<alpha> \<^sub><\<rightarrow>\<^bsup>M\<^esup> (P,leq) \<equiv> mono_seqspace_rel(M,\<alpha>,P,leq)"

abbreviation
  mono_seqspace_r_set (\<open>_ \<^sub><\<rightarrow>\<^bsup>_\<^esup> '(_,_')\<close> [61] 60) where
  "\<alpha> \<^sub><\<rightarrow>\<^bsup>M\<^esup> (P,leq) \<equiv> mono_seqspace_rel(##M,\<alpha>,P,leq)"

lemma mono_seqspaceI[intro!]:
  includes mono_map_rules
  assumes "f: A\<rightarrow>P" "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> x<y \<Longrightarrow> \<langle>f`x, f`y\<rangle> \<in> leq" "Ord(A)"
  shows  "f: A \<^sub><\<rightarrow> (P,leq)"
  using ltI[OF _ Ord_in_Ord[of A], THEN [3] assms(2)] assms(1,3)
  unfolding mono_seqspace_def by auto

lemma (in M_ZF_library) mono_seqspace_rel_char:
  assumes "M(A)" "M(P)" "M(leq)"
  shows "A \<^sub><\<rightarrow>\<^bsup>M\<^esup> (P,leq) = {f\<in>A \<^sub><\<rightarrow> (P,leq). M(f)}"
  using assms mono_map_rel_char
  unfolding mono_seqspace_def mono_seqspace_rel_def by simp

lemma (in M_ZF_library) mono_seqspace_relI[intro!]:
  assumes "f: A\<rightarrow>\<^bsup>M\<^esup> P" "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> x<y \<Longrightarrow> \<langle>f`x, f`y\<rangle> \<in> leq"
    "Ord(A)" "M(A)" "M(P)" "M(leq)"
  shows  "f: A \<^sub><\<rightarrow>\<^bsup>M\<^esup> (P,leq)"
  using mono_seqspace_rel_char function_space_rel_char assms by auto

lemma mono_seqspace_is_fun[dest]:
  includes mono_map_rules
  shows "j: A \<^sub><\<rightarrow> (P,leq) \<Longrightarrow> j: A\<rightarrow> P"
  unfolding mono_seqspace_def by auto

lemma mono_map_lt_le_is_mono[dest]:
  includes mono_map_rules
  assumes "j: A \<^sub><\<rightarrow> (P,leq)" "a\<in>A" "c\<in>A" "a\<le>c" "Ord(A)" "refl(P,leq)"
  shows "\<langle>j`a,j`c\<rangle> \<in> leq"
  using assms mono_map_increasing unfolding mono_seqspace_def refl_def
  by (cases "a=c") (auto dest:ltD)

lemma (in M_ZF_library) mem_mono_seqspace_abs[absolut]:
  assumes "M(f)" "M(A)" "M(P)" "M(leq)"
  shows  "f:A \<^sub><\<rightarrow>\<^bsup>M\<^esup> (P,leq) \<longleftrightarrow>  f: A \<^sub><\<rightarrow> (P,leq)"
  using assms mono_map_rel_char unfolding mono_seqspace_def mono_seqspace_rel_def
  by (simp)

definition
  mono_map_lt_le :: "[i,i] \<Rightarrow> i" (infixr \<open>\<^sub><\<rightarrow>\<^sub>\<le>\<close> 60) where
  "\<alpha> \<^sub><\<rightarrow>\<^sub>\<le> \<beta> \<equiv> \<alpha> \<^sub><\<rightarrow> (\<beta>,lerel(\<beta>))"

lemma mono_map_lt_leI[intro!]:
  includes mono_map_rules
  assumes "f: A\<rightarrow>B" "\<And>x y. x\<in>A \<Longrightarrow> y\<in>A \<Longrightarrow> x<y \<Longrightarrow> f`x \<le> f`y" "Ord(A)" "Ord(B)"
  shows  "f: A \<^sub><\<rightarrow>\<^sub>\<le> B"
  using assms
  unfolding mono_map_lt_le_def by auto

\<comment> \<open>Kunen IV.7.13, with ``$\kappa$'' in place of ``$\lambda$''\<close>
definition
  kappa_closed :: "[i,i,i] \<Rightarrow> o" (\<open>_-closed'(_,_')\<close>) where
  "\<kappa>-closed(P,leq) \<equiv> \<forall>\<delta>. \<delta><\<kappa> \<longrightarrow> (\<forall>f\<in>\<delta> \<^sub><\<rightarrow> (P,converse(leq)). \<exists>q\<in>P. \<forall>\<alpha>\<in>\<delta>. \<langle>q,f`\<alpha>\<rangle>\<in>leq)"

relativize functional "kappa_closed" "kappa_closed_rel"
relationalize "kappa_closed_rel" "is_kappa_closed"
synthesize "is_kappa_closed" from_definition assuming "nonempty"

abbreviation
  kappa_closed_r (\<open>_-closed\<^bsup>_\<^esup>'(_,_')\<close> [61] 60) where
  "\<kappa>-closed\<^bsup>M\<^esup>(P,leq) \<equiv> kappa_closed_rel(M,\<kappa>,P,leq)"

abbreviation
  kappa_closed_r_set (\<open>_-closed\<^bsup>_\<^esup>'(_,_')\<close> [61] 60) where
  "\<kappa>-closed\<^bsup>M\<^esup>(P,leq) \<equiv> kappa_closed_rel(##M,\<kappa>,P,leq)"

lemma (in forcing_data3) forcing_a_value:
  assumes "p \<tturnstile> \<cdot>0:1\<rightarrow>2\<cdot> [f_dot, A\<^sup>v, B\<^sup>v]" "a \<in> A"
    "q \<preceq> p" "q \<in> \<bbbP>" "p\<in>\<bbbP>" "f_dot \<in> M" "A\<in>M" "B\<in>M"
  shows "\<exists>d\<in>\<bbbP>. \<exists>b\<in>B. d \<preceq> q \<and> d \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, a\<^sup>v, b\<^sup>v]"
    (* \<comment> \<open>Old neater version, but harder to use
    (without the assumptions on \<^term>\<open>q\<close>):\<close>
    "dense_below({q \<in> \<bbbP>. \<exists>b\<in>B. q \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, a\<^sup>v, b\<^sup>v]}, p)" *)
proof -
  from assms
  have "q \<tturnstile> \<cdot>0:1\<rightarrow>2\<cdot> [f_dot, A\<^sup>v, B\<^sup>v]"
    using strengthening_lemma[of p "\<cdot>0:1\<rightarrow>2\<cdot>" q "[f_dot, A\<^sup>v, B\<^sup>v]"]
      typed_function_type arity_typed_function_fm
    by (auto simp: union_abs2 union_abs1)
  from \<open>a\<in>A\<close> \<open>A\<in>M\<close>
  have "a\<in>M" by (auto dest:transitivity)
  from \<open>q\<in>\<bbbP>\<close>
  text\<open>Here we're using countability (via the existence of generic filters)
    of \<^term>\<open>M\<close> as a shortcut, to avoid a further density argument.\<close>
  obtain G where "M_generic(G)" "q\<in>G"
    using generic_filter_existence by blast
  then
  interpret G_generic3_AC _ _ _ _ _ G by unfold_locales
  include G_generic1_lemmas
  note \<open>q\<in>G\<close>
  moreover
  note \<open>q \<tturnstile> \<cdot>0:1\<rightarrow>2\<cdot> [f_dot, A\<^sup>v, B\<^sup>v]\<close> \<open>M_generic(G)\<close>
  moreover
  note \<open>q\<in>\<bbbP>\<close> \<open>f_dot\<in>M\<close> \<open>B\<in>M\<close> \<open>A\<in>M\<close>
  moreover from this
  have "map(val( G), [f_dot, A\<^sup>v, B\<^sup>v]) \<in> list(M[G])" by simp
  moreover from calculation
  have "val(G,f_dot) : A \<rightarrow>\<^bsup>M[G]\<^esup> B"
    using truth_lemma[of "\<cdot>0:1\<rightarrow>2\<cdot>" "[f_dot, A\<^sup>v, B\<^sup>v]", THEN iffD1]
      typed_function_type arity_typed_function_fm val_check[OF one_in_G one_in_P]
    by (auto simp: union_abs2 union_abs1 ext.mem_function_space_rel_abs)
  moreover
  note \<open>a \<in> M\<close>
  moreover from calculation and \<open>a\<in>A\<close>
  have "val(G,f_dot) ` a \<in> B" (is "?b \<in> B")
    by (simp add: ext.mem_function_space_rel_abs)
  moreover from calculation
  have "?b \<in> M" by (auto dest:transitivity)
  moreover from calculation
  have "M[G], map(val(G), [f_dot, a\<^sup>v, ?b\<^sup>v]) \<Turnstile> \<cdot>0`1 is 2\<cdot>"
    by simp
  ultimately
  obtain r where "r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, a\<^sup>v, ?b\<^sup>v]" "r\<in>G" "r\<in>\<bbbP>"
    using truth_lemma[of "\<cdot>0`1 is 2\<cdot>" "[f_dot, a\<^sup>v, ?b\<^sup>v]", THEN iffD2]
      fun_apply_type arity_fun_apply_fm val_check[OF one_in_G one_in_P]
      G_subset_P
    by (auto simp: union_abs2 union_abs1 ext.mem_function_space_rel_abs)
  moreover from this and \<open>q\<in>G\<close>
  obtain d where "d\<preceq>q" "d\<preceq>r" "d\<in>\<bbbP>" by force
  moreover
  note \<open>f_dot\<in>M\<close> \<open>a\<in>M\<close> \<open>?b\<in>B\<close> \<open>B\<in>M\<close>
  moreover from calculation
  have "d \<preceq> q \<and> d \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, a\<^sup>v, ?b\<^sup>v]"
    using fun_apply_type arity_fun_apply_fm
      strengthening_lemma[of r "\<cdot>0`1 is 2\<cdot>" d "[f_dot, a\<^sup>v, ?b\<^sup>v]"]
    by (auto dest:transitivity simp add: union_abs2 union_abs1)
  ultimately
  show ?thesis by auto
qed

locale M_master_CH = M_master + M_library_DC

sublocale M_ZFC2_ground_CH_trans \<subseteq> M_master_CH "##M"
  using replacement_dcwit_repl_body
  by unfold_locales (simp_all add:sep_instances del:setclass_iff
      add: transrec_replacement_def wfrec_replacement_def dcwit_repl_body_def)

context G_generic3_AC_CH begin

context
  includes G_generic1_lemmas
begin

lemma separation_check_snd_aux:
  assumes "f_dot\<in>M" "\<tau>\<in>M" "\<chi>\<in>formula" "arity(\<chi>) \<le> 7"
  shows "separation(##M, \<lambda>r. M, [fst(r), \<bbbP>, leq, \<one>, f_dot, \<tau>, snd(r)\<^sup>v] \<Turnstile> \<chi>)"
proof -
  let ?f_fm="fst_fm(1,0)"
  let ?g_fm="hcomp_fm(check_fm(6),snd_fm,2,0)"
  note assms
  moreover
  have "?f_fm \<in> formula" "arity(?f_fm) \<le> 7" "?g_fm \<in> formula" "arity(?g_fm) \<le> 8"
    using ord_simp_union
    unfolding hcomp_fm_def
    by (simp_all add:arity)
  ultimately
  show ?thesis
    using separation_sat_after_function
    using fst_abs snd_abs sats_snd_fm sats_check_fm check_abs
    unfolding hcomp_fm_def
    by simp
qed

lemma separation_check_fst_snd_aux :
  assumes "f_dot\<in>M" "r\<in>M" "\<chi>\<in>formula" "arity(\<chi>) \<le> 7"
  shows "separation(##M, \<lambda>p. M, [r, \<bbbP>, leq, \<one>, f_dot, fst(p)\<^sup>v, snd(p)\<^sup>v] \<Turnstile> \<chi>)"
proof -
  let ?\<rho>="\<lambda>z. [r, \<bbbP>, leq, \<one>, f_dot, fst(z)\<^sup>v, snd(z)\<^sup>v]"
  let ?\<rho>'="\<lambda>z. [fst(z)\<^sup>v, \<bbbP>, leq, \<one>, f_dot, r, snd(z)\<^sup>v]"
  let ?\<phi>=" (\<cdot>\<exists>(\<cdot>\<exists>(\<cdot>\<exists>(\<cdot>\<exists>(\<cdot>\<exists>(\<cdot>\<exists>\<cdot>\<cdot>0 = 11\<cdot> \<and> \<cdot>\<cdot>1 = 7\<cdot> \<and> \<cdot>\<cdot>2 = 8\<cdot> \<and> \<cdot>\<cdot>3 = 9\<cdot> \<and> \<cdot>\<cdot>4 = 10\<cdot> \<and> \<cdot>\<cdot>5 = 6\<cdot> \<and>
    (\<lambda>p. incr_bv(p)`6)^6 (\<chi>) \<cdot>\<cdot>\<cdot>\<cdot>\<cdot>\<cdot>\<cdot>)\<cdot>)\<cdot>)\<cdot>)\<cdot>)\<cdot>)"
  let ?f_fm="hcomp_fm(check_fm(5),fst_fm,1,0)"
  let ?g_fm="hcomp_fm(check_fm(6),snd_fm,2,0)"
  note assms
  moreover
  have "?f_fm \<in> formula" "arity(?f_fm) \<le> 7" "?g_fm \<in> formula" "arity(?g_fm) \<le> 8"
    using ord_simp_union
    unfolding hcomp_fm_def
    by (simp_all add:arity)
  moreover from assms
  have fm:"?\<phi>\<in>formula" by simp
  moreover from \<open>\<chi> \<in> formula\<close> \<open>arity(\<chi>) \<le> 7\<close>
  have "arity(\<chi>) = 0 \<or> arity(\<chi>) = 1 \<or> arity(\<chi>) = 2 \<or> arity(\<chi>) = 3
    \<or> arity(\<chi>) = 4 \<or> arity(\<chi>) = 5 \<or> arity(\<chi>) = 6 \<or> arity(\<chi>) = 7"
    unfolding lt_def by auto
  with calculation and \<open>\<chi> \<in> formula\<close>
  have ar:"arity(?\<phi>) \<le> 7"
    using arity_incr_bv_lemma by safe (simp_all add: arity ord_simp_union)
  moreover from calculation
  have sep:"separation(##M,\<lambda>z. M,?\<rho>'(z)\<Turnstile>?\<phi>)"
    using separation_sat_after_function sats_check_fm check_abs
      fst_abs snd_abs
    unfolding hcomp_fm_def
    by simp
  moreover from assms
  have "?\<rho>(z) \<in> list(M)" if "(##M)(z)" for z
    using that by simp
  moreover from calculation and \<open>r \<in> M\<close> \<open>\<chi> \<in> formula\<close>
  have "(M,?\<rho>(z) \<Turnstile> \<chi>) \<longleftrightarrow> (M,?\<rho>'(z)\<Turnstile>?\<phi>)" if "(##M)(z)" for z
    using that sats_incr_bv_iff[of _ _ M _ "[_,_,_,_,_,_]"]
    by simp
  ultimately
  show ?thesis
    using separation_cong[THEN iffD1,OF _ sep]
    by simp
qed

lemma separation_leq_and_forces_apply_aux:
  assumes "f_dot\<in>M" "B\<in>M"
  shows "\<forall>n\<in>M. separation(##M, \<lambda>x. snd(x) \<preceq> fst(x) \<and>
          (\<exists>b\<in>B. M, [snd(x), \<bbbP>, leq, \<one>, f_dot, (\<Union>(n))\<^sup>v, b\<^sup>v] \<Turnstile> forces(\<cdot>0`1 is 2\<cdot> )))"
proof -
  have pred_nat_closed: "pred(n)\<in>M" if "n\<in>M" for n
    using nat_case_closed that
    unfolding pred_def
    by auto
  have "separation(##M, \<lambda>z. M, [snd(fst(z)), \<bbbP>, leq, \<one>, f_dot, \<tau>, snd(z)\<^sup>v] \<Turnstile> \<chi>)"
    if "\<chi>\<in>formula" "arity(\<chi>) \<le> 7" "\<tau>\<in>M" for \<chi> \<tau>
  proof -
    let ?f_fm="hcomp_fm(snd_fm,fst_fm,1,0)"
    let ?g_fm="hcomp_fm(check_fm(6),snd_fm,2,0)"
    note assms
    moreover
    have "?f_fm \<in> formula" "arity(?f_fm) \<le> 7" "?g_fm \<in> formula" "arity(?g_fm) \<le> 8"
      using ord_simp_union
      unfolding hcomp_fm_def
      by (simp_all add:arity)
    ultimately
    show ?thesis
      using separation_sat_after_function sats_check_fm check_abs fst_abs snd_abs that
      unfolding hcomp_fm_def
      by simp
  qed
  with assms
  show ?thesis
    using separation_in lam_replacement_constant lam_replacement_snd lam_replacement_fst
      lam_replacement_product pred_nat_closed
      arity_forces[of " \<cdot>0`1 is 2\<cdot>"] arity_fun_apply_fm[of 0 1 2] ord_simp_union
    by(clarify,rule_tac separation_conj,simp_all,rule_tac separation_bex,simp_all)
qed

lemma separation_leq_and_forces_apply_aux':
  assumes "f_dot\<in>M" "p\<in>M" "B\<in>M"
  shows "separation
     (##M, \<lambda>p .  snd(snd(p)) \<preceq> fst(snd(p)) \<and>
    (\<exists>b\<in>B. M, [snd(snd(p)), \<bbbP>, leq, \<one>, f_dot, (\<Union>fst(p))\<^sup>v, b\<^sup>v] \<Turnstile> forces(\<cdot>0`1 is 2\<cdot> )))"
proof -
  have "separation(##M, \<lambda>z. M, [snd(snd(fst(z))), \<bbbP>, leq, \<one>, f_dot, (\<Union>fst(fst(z)))\<^sup>v, snd(z)\<^sup>v] \<Turnstile> \<chi>)"
    if "\<chi>\<in>formula" "arity(\<chi>) \<le> 7" for \<chi>
  proof -
    let ?f_fm="hcomp_fm(snd_fm,hcomp_fm(snd_fm,fst_fm),1,0)"
    let ?g="\<lambda>z . (\<Union>(fst(fst(z))))\<^sup>v"
    let ?g_fm="hcomp_fm(check_fm(6),hcomp_fm(big_union_fm,hcomp_fm(fst_fm,fst_fm)),2,0)"
    let ?h_fm="hcomp_fm(check_fm(7),snd_fm,3,0)"
    note assms
    moreover
    have f_fm_facts:"?f_fm \<in> formula" "arity(?f_fm) \<le> 6"
      using ord_simp_union
      unfolding hcomp_fm_def
      by (simp_all add:arity)
    moreover from assms
    have "?g_fm \<in> formula" "arity(?g_fm) \<le> 7" "?h_fm \<in> formula" "arity(?h_fm) \<le> 8"
      using ord_simp_union
      unfolding hcomp_fm_def
      by (simp_all add:arity)
    ultimately
    show ?thesis
      using separation_sat_after_function3[OF _ _ _ f_fm_facts] check_abs
        sats_check_fm that fst_abs snd_abs sats_fst_fm sats_snd_fm
      unfolding hcomp_fm_def
      by simp
  qed
  with assms
  show ?thesis
    using
      separation_conj separation_bex
      lam_replacement_constant lam_replacement_hcomp
      lam_replacement_fst lam_replacement_snd
      arity_forces[of " \<cdot>0`1 is 2\<cdot>"] arity_fun_apply_fm[of 0 1 2] ord_simp_union
      separation_in[OF _ lam_replacement_product]
    by simp
qed

lemma separation_closed_leq_and_forces_eq_check_aux :
  assumes "A\<in>M" "r\<in>G" "\<tau> \<in> M"
  shows "(##M)({q\<in>\<bbbP>. \<exists>h\<in>A. q \<preceq> r \<and> q \<tturnstile> \<cdot>0 = 1\<cdot> [\<tau>, h\<^sup>v]})"
proof -
  have "separation(##M, \<lambda>z. M, [fst(z), \<bbbP>, leq, \<one>, \<tau>, snd(z)\<^sup>v] \<Turnstile> \<chi>)" if
    "\<chi>\<in>formula" "arity(\<chi>) \<le> 6" for \<chi>
  proof -
    let ?f_fm="fst_fm(1,0)"
    let ?g_fm="hcomp_fm(check_fm(6),snd_fm,2,0)"
    note assms
    moreover
    have "?f_fm \<in> formula" "arity(?f_fm) \<le> 6" "?g_fm \<in> formula" "arity(?g_fm) \<le> 7"
      using ord_simp_union
      unfolding hcomp_fm_def
      by (simp_all add:arity)
    ultimately
    show ?thesis
      using separation_sat_after_function_1 sats_fst_fm that
        fst_abs snd_abs sats_snd_fm sats_check_fm check_abs
      unfolding hcomp_fm_def
      by simp
  qed
  with assms
  show ?thesis
    using separation_conj separation_in G_subset_M[THEN subsetD]
      lam_replacement_constant lam_replacement_fst lam_replacement_product
      arity_forces[of "\<cdot>0 = 1\<cdot>",simplified] ord_simp_union
    by(rule_tac separation_closed[OF separation_bex],simp_all)
qed

lemma separation_closed_forces_apply_aux:
  assumes "B\<in>M" "f_dot\<in>M" "r\<in>M"
  shows "(##M)({\<langle>n,b\<rangle> \<in> \<omega> \<times> B. r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, n\<^sup>v, b\<^sup>v]})"
  using nat_in_M assms transitivity[OF _ \<open>B\<in>M\<close>] nat_into_M separation_check_fst_snd_aux
    arity_forces[of " \<cdot>0`1 is 2\<cdot>"] arity_fun_apply_fm[of 0 1 2] ord_simp_union
  unfolding split_def
  by simp_all

\<comment> \<open>Kunen IV.6.9 (3)$\Rightarrow$(2), with general domain.\<close>
lemma kunen_IV_6_9_function_space_rel_eq:
  assumes "\<And>p \<tau>. p \<tturnstile> \<cdot>0:1\<rightarrow>2\<cdot> [\<tau>, A\<^sup>v, B\<^sup>v] \<Longrightarrow> p\<in>\<bbbP> \<Longrightarrow> \<tau> \<in> M \<Longrightarrow>
    \<exists>q\<in>\<bbbP>. \<exists>h\<in>A \<rightarrow>\<^bsup>M\<^esup> B. q \<preceq> p \<and>  q \<tturnstile> \<cdot>0 = 1\<cdot> [\<tau>, h\<^sup>v]" "A\<in>M" "B\<in>M"
  shows
    "A \<rightarrow>\<^bsup>M\<^esup> B = A \<rightarrow>\<^bsup>M[G]\<^esup> B"
proof (intro equalityI; clarsimp simp add:
    assms function_space_rel_char ext.function_space_rel_char)
  fix f
  assume "f \<in> A \<rightarrow> B" "f \<in> M[G]"
  moreover from this
  obtain \<tau> where "val(G,\<tau>) = f" "\<tau> \<in> M"
    using GenExtD by force
  moreover from calculation and \<open>A\<in>M\<close> \<open>B\<in>M\<close>
  obtain r where "r \<tturnstile> \<cdot>0:1\<rightarrow>2\<cdot> [\<tau>, A\<^sup>v, B\<^sup>v]" "r\<in>G"
    using truth_lemma[of "\<cdot>0:1\<rightarrow>2\<cdot>" "[\<tau>, A\<^sup>v, B\<^sup>v]"]
      typed_function_type arity_typed_function_fm val_check[OF one_in_G one_in_P]
    by (auto simp: union_abs2 union_abs1)
  moreover from \<open>A\<in>M\<close> \<open>B\<in>M\<close> \<open>r\<in>G\<close> \<open>\<tau> \<in> M\<close>
  have "{q\<in>\<bbbP>. \<exists>h\<in>A \<rightarrow>\<^bsup>M\<^esup> B. q \<preceq> r \<and> q \<tturnstile> \<cdot>0 = 1\<cdot> [\<tau>, h\<^sup>v]} \<in> M" (is "?D \<in> M")
    using separation_closed_leq_and_forces_eq_check_aux by auto
  moreover from calculation and assms(2-)
  have "dense_below(?D, r)"
    using strengthening_lemma[of r "\<cdot>0:1\<rightarrow>2\<cdot>" _ "[\<tau>, A\<^sup>v, B\<^sup>v]", THEN assms(1)[of _ \<tau>]]
      leq_transD generic_dests(1)[of r]
    by (auto simp: union_abs2 union_abs1 typed_function_type arity_typed_function_fm) blast
  moreover from calculation
  obtain q h where "h\<in>A \<rightarrow>\<^bsup>M\<^esup> B" "q \<tturnstile> \<cdot>0 = 1\<cdot> [\<tau>, h\<^sup>v]" "q \<preceq> r" "q\<in>\<bbbP>" "q\<in>G"
    using generic_inter_dense_below[of ?D r] by blast
  note \<open>q \<tturnstile> \<cdot>0 = 1\<cdot> [\<tau>, h\<^sup>v]\<close> \<open>\<tau>\<in>M\<close> \<open>h\<in>A \<rightarrow>\<^bsup>M\<^esup> B\<close> \<open>A\<in>M\<close> \<open>B\<in>M\<close> \<open>q\<in>G\<close>
  moreover from this
  have "map(val(G), [\<tau>, h\<^sup>v]) \<in> list(M[G])" "h\<in>M"
    by (auto dest:transitivity)
  ultimately
  have "h = f"
    using truth_lemma[of "\<cdot>0=1\<cdot>" "[\<tau>, h\<^sup>v]"] val_check[OF one_in_G one_in_P]
    by (auto simp: ord_simp_union)
  with \<open>h\<in>M\<close>
  show "f \<in> M" by simp
qed

subsection\<open>$(\omega+1)$-Closed notions preserve countable sequences\<close>

\<comment> \<open>Kunen IV.7.15, only for countable sequences\<close>
lemma succ_omega_closed_imp_no_new_nat_sequences:
  assumes "succ(\<omega>)-closed\<^bsup>M\<^esup>(\<bbbP>,leq)" "f : \<omega> \<rightarrow> B" "f\<in>M[G]" "B\<in>M"
  shows "f\<in>M"
proof -
  (* Nice jEdit folding level to read this: 7 *)
  text\<open>The next long block proves that the assumptions of Lemma
  @{thm [source] kunen_IV_6_9_function_space_rel_eq} are satisfied.\<close>
  {
    fix p f_dot
    assume "p \<tturnstile> \<cdot>0:1\<rightarrow>2\<cdot> [f_dot, \<omega>\<^sup>v, B\<^sup>v]" "p\<in>\<bbbP>" "f_dot\<in>M"
    let ?subp="{q\<in>\<bbbP>. q \<preceq> p}"
    from \<open>p\<in>\<bbbP>\<close>
    have "?subp \<in> M"
      using first_section_closed[of \<bbbP> p "converse(leq)"]
      by (auto dest:transitivity)
    define S where "S \<equiv> \<lambda>n\<in>nat.
    {\<langle>q,r\<rangle> \<in> ?subp\<times>?subp. r \<preceq> q \<and> (\<exists>b\<in>B. r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, (\<Union>(n))\<^sup>v, b\<^sup>v])}"
      (is "S \<equiv> \<lambda>n\<in>nat. ?Y(n)")
    define S' where "S' \<equiv> \<lambda>n\<in>nat.
    {\<langle>q,r\<rangle> \<in> ?subp\<times>?subp. r \<preceq> q \<and> (\<exists>b\<in>B. r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, (pred(n))\<^sup>v, b\<^sup>v])}"
      \<comment> \<open>Towards proving \<^term>\<open>S\<in>M\<close>.\<close>
    moreover
    have "S = S'"
      unfolding S_def S'_def using pred_nat_eq lam_cong by auto
    moreover from \<open>B\<in>M\<close> \<open>?subp\<in>M\<close> \<open>f_dot\<in>M\<close>
    have "{r \<in> ?subp. \<exists>b\<in>B. r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, (\<Union>(n))\<^sup>v, b\<^sup>v]} \<in> M" (is "?X(n) \<in> M")
      if "n\<in>\<omega>" for n
      using that separation_check_snd_aux nat_into_M ord_simp_union
        arity_forces[of " \<cdot>0`1 is 2\<cdot>"] arity_fun_apply_fm
      by(rule_tac separation_closed[OF separation_bex,simplified], simp_all)
    moreover
    have "?Y(n) = (?subp \<times> ?X(n)) \<inter> converse(leq)" for n
      by (intro equalityI) auto
    moreover
    note \<open>?subp \<in> M\<close> \<open>B\<in>M\<close> \<open>p\<in>\<bbbP>\<close> \<open>f_dot\<in>M\<close>
    moreover from calculation
    have "n \<in> \<omega> \<Longrightarrow> ?Y(n) \<in> M" for n
      using nat_into_M by simp
    moreover from calculation
    have "S \<in> M"
      using  separation_leq_and_forces_apply_aux separation_leq_and_forces_apply_aux'
        transitivity[OF \<open>p\<in>\<bbbP>\<close>]
      unfolding S_def split_def
      by(rule_tac lam_replacement_Collect'[THEN lam_replacement_imp_lam_closed,simplified], simp_all)
    ultimately
    have "S' \<in> M"
      by simp
    from \<open>p\<in>\<bbbP>\<close> \<open>f_dot\<in>M\<close> \<open>p \<tturnstile> \<cdot>0:1\<rightarrow>2\<cdot> [f_dot, \<omega>\<^sup>v, B\<^sup>v]\<close> \<open>B\<in>M\<close>
    have exr:"\<exists>r\<in>\<bbbP>. r \<preceq> q \<and> (\<exists>b\<in>B. r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, pred(n)\<^sup>v, b\<^sup>v])"
      if "q \<preceq> p" "q\<in>\<bbbP>" "n\<in>\<omega>" for q n
      using that forcing_a_value by (auto dest:transitivity)
    have "\<forall>q\<in>?subp. \<forall>n\<in>\<omega>. \<exists>r\<in>?subp. \<langle>q,r\<rangle> \<in> S'`n"
    proof -
      {
        fix q n
        assume "q \<in> ?subp" "n\<in>\<omega>"
        moreover from this
        have "q \<preceq> p" "q \<in> \<bbbP>" "pred(n) = \<Union>n"
          using pred_nat_eq by simp_all
        moreover from calculation and exr
        obtain r where MM:"r \<preceq> q" "\<exists>b\<in>B. r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, pred(n)\<^sup>v, b\<^sup>v]" "r\<in>\<bbbP>"
          by blast
        moreover from calculation \<open>q \<preceq> p\<close> \<open>p \<in> \<bbbP>\<close>
        have "r \<preceq> p"
          using leq_transD[of r q p] by auto
        ultimately
        have "\<exists>r\<in>?subp. r \<preceq> q \<and> (\<exists>b\<in>B. r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, (pred(n))\<^sup>v, b\<^sup>v])"
          by auto
      }
      then
      show ?thesis
        unfolding S'_def by simp
    qed
    with \<open>p\<in>\<bbbP>\<close> \<open>?subp \<in> M\<close> \<open>S' \<in> M\<close>
    obtain g where "g \<in> \<omega> \<rightarrow>\<^bsup>M\<^esup> ?subp" "g`0 = p" "\<forall>n \<in> nat. \<langle>g`n,g`succ(n)\<rangle>\<in>S'`succ(n)"
      using sequence_DC[simplified] refl_leq[of p] by blast
    moreover from this and \<open>?subp \<in> M\<close>
    have "g : \<omega> \<rightarrow> \<bbbP>" "g \<in> M"
      using fun_weaken_type[of g \<omega> ?subp \<bbbP>] function_space_rel_char by auto
    ultimately
    have "g : \<omega> \<^sub><\<rightarrow>\<^bsup>M\<^esup> (\<bbbP>,converse(leq))"
      using decr_succ_decr[of g] leq_preord
      unfolding S'_def by (auto simp:absolut intro:leI)
    moreover from \<open>succ(\<omega>)-closed\<^bsup>M\<^esup>(\<bbbP>,leq)\<close> and this
    have "\<exists>q\<in>M. q \<in> \<bbbP> \<and> (\<forall>\<alpha>\<in>M. \<alpha> \<in> \<omega> \<longrightarrow> q \<preceq> g ` \<alpha>)"
      using transitivity[simplified, of g] mono_seqspace_rel_closed[of \<omega> _ "converse(leq)"]
      unfolding kappa_closed_rel_def
      by auto
    ultimately
    obtain r where "r\<in>\<bbbP>" "r\<in>M" "\<forall>n\<in>\<omega>. r \<preceq> g`n"
      using nat_into_M by auto
    with \<open>g`0 = p\<close>
    have "r \<preceq> p"
      by blast
    let ?h="{\<langle>n,b\<rangle> \<in> \<omega> \<times> B. r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, n\<^sup>v, b\<^sup>v]}"
    have "function(?h)"
    proof (rule_tac functionI, rule_tac ccontr, auto simp del: app_Cons)
      fix n b b'
      assume "n \<in> \<omega>" "b \<noteq> b'" "b \<in> B" "b' \<in> B"
      moreover
      assume "r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, n\<^sup>v, b\<^sup>v]" "r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, n\<^sup>v, b'\<^sup>v]"
      moreover
      note \<open>r \<in> \<bbbP>\<close>
      moreover from this
      have "\<not> r \<bottom> r"
        by (auto intro!:refl_leq)
      moreover
      note \<open>f_dot\<in>M\<close> \<open>B\<in>M\<close>
      ultimately
      show False
        using forces_neq_apply_imp_incompatible[of r f_dot "n\<^sup>v" b r b']
          transitivity[of _ B] by (auto dest:transitivity)
    qed
    moreover
    have "range(?h) \<subseteq> B"
      by auto
    moreover
    have "domain(?h) = \<omega>"
    proof -
      {
        fix n
        assume "n \<in> \<omega>"
        moreover from this
        have 1:"(\<Union>(n)) = pred(n)"
          using pred_nat_eq by simp
        moreover from calculation and \<open>\<forall>n \<in> nat. \<langle>g`n,g`succ(n)\<rangle>\<in>S'`succ(n)\<close>
        obtain b where "g`(succ(n)) \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, n\<^sup>v, b\<^sup>v]" "b\<in>B"
          unfolding S'_def by auto
        moreover from \<open>B\<in>M\<close> and calculation
        have "b \<in> M" "n \<in> M"
          by (auto dest:transitivity)
        moreover
        note \<open>g : \<omega> \<rightarrow> \<bbbP>\<close> \<open>\<forall>n\<in>\<omega>. r \<preceq> g`n\<close> \<open>r\<in>\<bbbP>\<close> \<open>f_dot\<in>M\<close>
        moreover from calculation
        have "r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, n\<^sup>v, b\<^sup>v]"
          using fun_apply_type arity_fun_apply_fm
            strengthening_lemma[of "g`succ(n)" "\<cdot>0`1 is 2\<cdot>" r "[f_dot, n\<^sup>v, b\<^sup>v]"]
          by (simp add: union_abs2 union_abs1)
        ultimately
        have "\<exists>b\<in>B. r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, n\<^sup>v, b\<^sup>v]"
          by auto
      }
      then
      show ?thesis
        by force
    qed
    moreover
    have "relation(?h)"
      unfolding relation_def by simp
    moreover from \<open>f_dot\<in>M\<close> \<open>r\<in>M\<close> \<open>B\<in>M\<close>
    have "?h \<in> M"
      using separation_closed_forces_apply_aux by simp
    moreover
    note \<open>B \<in> M\<close>
    ultimately
    have "?h: \<omega> \<rightarrow>\<^bsup>M\<^esup> B"
      using function_imp_Pi[THEN fun_weaken_type[of ?h _ "range(?h)" B]]
        function_space_rel_char by simp
    moreover
    note \<open>p \<tturnstile> \<cdot>0:1\<rightarrow>2\<cdot> [f_dot, \<omega>\<^sup>v, B\<^sup>v]\<close> \<open>r \<preceq> p\<close> \<open>r\<in>\<bbbP>\<close> \<open>p\<in>\<bbbP>\<close> \<open>f_dot\<in>M\<close> \<open>B\<in>M\<close>
    moreover from this
    have "r \<tturnstile> \<cdot>0:1\<rightarrow>2\<cdot> [f_dot, \<omega>\<^sup>v, B\<^sup>v]"
      using strengthening_lemma[of p "\<cdot>0:1\<rightarrow>2\<cdot>" r "[f_dot, \<omega>\<^sup>v, B\<^sup>v]"]
        typed_function_type arity_typed_function_fm
      by (auto simp: union_abs2 union_abs1)
    moreover
    note \<open>?h\<in>M\<close>
    moreover from calculation
    have "r \<tturnstile> \<cdot>0 = 1\<cdot> [f_dot, ?h\<^sup>v]"
    proof (intro definition_of_forcing[THEN iffD2] allI impI,
        simp_all add:union_abs2 union_abs1 del:app_Cons)
      fix H
      let ?f="val(H,f_dot)"
      assume "M_generic(H) \<and> r \<in> H"
      moreover from this
      interpret g:G_generic1 _ _ _ _ _ H
        by unfold_locales simp
      note \<open>r\<in>\<bbbP>\<close> \<open>f_dot\<in>M\<close> \<open>B\<in>M\<close>
      moreover from calculation
      have "map(val(H), [f_dot, \<omega>\<^sup>v, B\<^sup>v]) \<in> list(M[H])" "r\<in>H"
        by simp_all
      moreover from calculation and \<open>r\<in>H\<close> and \<open>r \<tturnstile> \<cdot>0:1\<rightarrow>2\<cdot> [f_dot, \<omega>\<^sup>v, B\<^sup>v]\<close>
      have "?f : \<omega> \<rightarrow> B"
        using g.truth_lemma[of "\<cdot>0:1\<rightarrow>2\<cdot>" "[f_dot, \<omega>\<^sup>v, B\<^sup>v]",THEN iffD1] g.one_in_G one_in_P
          typed_function_type arity_typed_function_fm val_check
        by (auto simp: union_abs2 union_abs1)
      moreover
      have "?h`n = ?f`n" if "n \<in> \<omega>" for n
      proof -
        note \<open>n \<in> \<omega>\<close> \<open>domain(?h) = \<omega>\<close>
        moreover from this
        have "n\<in>domain(?h)"
          by simp
        moreover from this
        obtain b where "r \<tturnstile> \<cdot>0`1 is 2\<cdot> [f_dot, n\<^sup>v, b\<^sup>v]" "b\<in>B"
          by force
        moreover
        note \<open>function(?h)\<close>
        moreover from calculation
        have "b = ?h`n"
          using function_apply_equality by simp
        moreover
        note \<open>B \<in> M\<close>
        moreover from calculation
        have "?h`n \<in> M"
          by (auto dest:transitivity)
        moreover
        note \<open>f_dot \<in> M\<close> \<open>r \<in> \<bbbP>\<close> \<open>M_generic(H) \<and> r \<in> H\<close> \<open>map(val(H), [f_dot, \<omega>\<^sup>v, B\<^sup>v]) \<in> list(M[H])\<close>
        moreover from calculation
        have "[?f, n, ?h`n] \<in> list(M[H])"
          using M_subset_MG nat_into_M[of n] g.one_in_G by (auto dest:transitivity)
        ultimately
        show ?thesis
          using definition_of_forcing[of r "\<cdot>0`1 is 2\<cdot>" "[f_dot, n\<^sup>v, b\<^sup>v]",
              THEN iffD1, rule_format, of H]\<comment> \<open>without this line is slower\<close>
            val_check g.one_in_G one_in_P nat_into_M
          by (auto dest:transitivity simp add:fun_apply_type
              arity_fun_apply_fm union_abs2 union_abs1)
      qed
      with calculation and \<open>B\<in>M\<close> \<open>?h: \<omega> \<rightarrow>\<^bsup>M\<^esup> B\<close>
      have "?h = ?f"
        using function_space_rel_char
        by (rule_tac fun_extension[of ?h \<omega> "\<lambda>_.B" ?f]) auto
      ultimately
      show "?f = val(H, ?h\<^sup>v)"
        using val_check g.one_in_G one_in_P generic by simp
    qed
    ultimately
    have "\<exists>r\<in>\<bbbP>. \<exists>h\<in>\<omega> \<rightarrow>\<^bsup>M\<^esup> B. r \<preceq> p \<and> r \<tturnstile> \<cdot>0 = 1\<cdot> [f_dot, h\<^sup>v]"
      by blast
  }
  moreover
  note \<open>B \<in> M\<close> assms
  moreover from calculation
  have "f : \<omega> \<rightarrow>\<^bsup>M\<^esup> B"
    using kunen_IV_6_9_function_space_rel_eq function_space_rel_char
      ext.mem_function_space_rel_abs by auto
  ultimately
  show ?thesis
    by (auto dest:transitivity)
qed

declare mono_seqspace_rel_closed[rule del]
  \<comment> \<open>Mysteriously breaks the end of the next proof\<close>

lemma succ_omega_closed_imp_no_new_reals:
  assumes "succ(\<omega>)-closed\<^bsup>M\<^esup>(\<bbbP>,leq)"
  shows "\<omega> \<rightarrow>\<^bsup>M\<^esup> 2 = \<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2"
proof -
  from assms
  have "\<omega> \<rightarrow>\<^bsup>M[G]\<^esup> 2 \<subseteq> \<omega> \<rightarrow>\<^bsup>M\<^esup> 2"
    using succ_omega_closed_imp_no_new_nat_sequences function_space_rel_char
      ext.function_space_rel_char Aleph_rel_succ Aleph_rel_zero
    by auto
  then
  show ?thesis
    using function_space_rel_transfer by (intro equalityI) auto
qed

lemma succ_omega_closed_imp_Aleph_1_preserved:
  assumes "succ(\<omega>)-closed\<^bsup>M\<^esup>(\<bbbP>,leq)"
  shows "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> = \<aleph>\<^bsub>1\<^esub>\<^bsup>M[G]\<^esup>"
proof -
  have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M[G]\<^esup> \<le> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
  proof (rule ccontr)
    assume "\<not> \<aleph>\<^bsub>1\<^esub>\<^bsup>M[G]\<^esup> \<le> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"
    then
    have "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup> < \<aleph>\<^bsub>1\<^esub>\<^bsup>M[G]\<^esup>"
      \<comment> \<open>Ridiculously complicated proof\<close>
      using Card_rel_is_Ord ext.Card_rel_is_Ord
        not_le_iff_lt[THEN iffD1] by auto
    then
    have "|\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>|\<^bsup>M[G]\<^esup> \<le> \<omega>"
      using ext.Card_rel_lt_csucc_rel_iff ext.Aleph_rel_zero
        ext.Aleph_rel_succ ext.Card_rel_nat
      by (auto intro!:ext.lt_csucc_rel_iff[THEN iffD1]
          intro:Card_rel_Aleph_rel[THEN Card_rel_is_Ord, of 1])
    then
    obtain f where "f \<in> inj(\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>,\<omega>)" "f \<in> M[G]"
      using ext.countable_rel_iff_cardinal_rel_le_nat[of "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>", THEN iffD2]
      unfolding countable_rel_def lepoll_rel_def
      by auto
    then
    obtain g where "g \<in> surj\<^bsup>M[G]\<^esup>(\<omega>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)"
      using ext.inj_rel_imp_surj_rel[of f _ \<omega>, OF _ zero_lt_Aleph_rel1[THEN ltD]]
      by auto
    moreover from this
    have "g : \<omega> \<rightarrow> \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>" "g \<in> M[G]"
      using ext.surj_rel_char surj_is_fun by simp_all
    moreover
    note \<open>succ(\<omega>)-closed\<^bsup>M\<^esup>(\<bbbP>,leq)\<close>
    ultimately
    have "g \<in> surj\<^bsup>M\<^esup>(\<omega>, \<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>)" "g \<in> M"
      using succ_omega_closed_imp_no_new_nat_sequences
        mem_surj_abs ext.mem_surj_abs by simp_all
    then
    show False
      using surj_rel_implies_cardinal_rel_le[of g \<omega> "\<aleph>\<^bsub>1\<^esub>\<^bsup>M\<^esup>"]
        Card_rel_nat[THEN Card_rel_cardinal_rel_eq] Card_rel_is_Ord
        not_le_iff_lt[THEN iffD2, OF _ _ nat_lt_Aleph_rel1]
      by simp
  qed
  then
  show ?thesis
    using Aleph_rel_le_Aleph_rel
    by (rule_tac le_anti_sym) simp
qed

end \<comment> \<open>bundle G\_generic1\_lemmas\<close>

end \<comment> \<open>\<^locale>\<open>G_generic3_AC\<close>\<close>

end