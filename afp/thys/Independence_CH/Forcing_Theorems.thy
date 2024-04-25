section\<open>The Forcing Theorems\<close>

theory Forcing_Theorems
  imports
    Cohen_Posets_Relative
    Forces_Definition
    Names

begin

context forcing_data1
begin

subsection\<open>The forcing relation in context\<close>

lemma separation_forces :
  assumes
    fty: "\<phi>\<in>formula" and
    far: "arity(\<phi>)\<le>length(env)" and
    envty: "env\<in>list(M)"
  shows
    "separation(##M,\<lambda>p. (p \<tturnstile> \<phi> env))"
  using separation_ax arity_forces far fty envty arity_forces_le
    transitivity[of _ \<bbbP>]
  by simp

lemma Collect_forces :
  assumes
    "\<phi>\<in>formula" and
    "arity(\<phi>)\<le>length(env)" and
    "env\<in>list(M)"
  shows
    "{p\<in>\<bbbP> . p \<tturnstile> \<phi> env} \<in> M"
  using assms separation_forces separation_closed
  by simp

lemma forces_mem_iff_dense_below:  "p\<in>\<bbbP> \<Longrightarrow> p forces\<^sub>a (t1 \<in> t2) \<longleftrightarrow> dense_below(
    {q\<in>\<bbbP>. \<exists>s. \<exists>r. r\<in>\<bbbP> \<and> \<langle>s,r\<rangle> \<in> t2 \<and> q\<preceq>r \<and> q forces\<^sub>a (t1 = s)}
    ,p)"
  using def_forces_mem[of p t1 t2] by blast

subsection\<open>Kunen 2013, Lemma IV.2.37(a)\<close>

lemma strengthening_eq:
  assumes "p\<in>\<bbbP>" "r\<in>\<bbbP>" "r\<preceq>p" "p forces\<^sub>a (t1 = t2)"
  shows "r forces\<^sub>a (t1 = t2)"
  using assms def_forces_eq[of _ t1 t2] leq_transD by blast
    (* Long proof *)
    (*
proof -
  {
    fix s q
    assume "q\<preceq> r" "q\<in>\<bbbP>"
    with assms
    have "q\<preceq>p"
      using leq_preord unfolding preorder_on_def trans_on_def by blast
    moreover
    note \<open>q\<in>\<bbbP>\<close> assms
    moreover
    assume "s\<in>domain(t1) \<union> domain(t2)"
    ultimately
    have "q forces\<^sub>a ( s \<in>  t1) \<longleftrightarrow> q forces\<^sub>a ( s \<in>  t2)"
      using def_forces_eq[of p t1 t2] by simp
  }
  with \<open>r\<in>\<bbbP>\<close>
  show ?thesis using def_forces_eq[of r t1 t2] by blast
qed
*)

subsection\<open>Kunen 2013, Lemma IV.2.37(a)\<close>
lemma strengthening_mem:
  assumes "p\<in>\<bbbP>" "r\<in>\<bbbP>" "r\<preceq>p" "p forces\<^sub>a (t1 \<in> t2)"
  shows "r forces\<^sub>a (t1 \<in> t2)"
  using assms forces_mem_iff_dense_below dense_below_under by auto

subsection\<open>Kunen 2013, Lemma IV.2.37(b)\<close>
lemma density_mem:
  assumes "p\<in>\<bbbP>"
  shows "p forces\<^sub>a (t1 \<in> t2)  \<longleftrightarrow> dense_below({q\<in>\<bbbP>. q forces\<^sub>a (t1 \<in> t2)},p)"
proof
  assume "p forces\<^sub>a (t1 \<in> t2)"
  with assms
  show "dense_below({q\<in>\<bbbP>. q forces\<^sub>a (t1 \<in> t2)},p)"
    using forces_mem_iff_dense_below strengthening_mem[of p] ideal_dense_below by auto
next
  assume "dense_below({q \<in> \<bbbP> . q forces\<^sub>a ( t1 \<in>  t2)}, p)"
  with assms
  have "dense_below({q\<in>\<bbbP>.
    dense_below({q'\<in>\<bbbP>. \<exists>s r. r \<in> \<bbbP> \<and> \<langle>s,r\<rangle>\<in>t2 \<and> q'\<preceq>r \<and> q' forces\<^sub>a (t1 = s)},q)
    },p)"
    using forces_mem_iff_dense_below by simp
  with assms
  show "p forces\<^sub>a (t1 \<in> t2)"
    using dense_below_dense_below forces_mem_iff_dense_below[of p t1 t2] by blast
qed

lemma aux_density_eq:
  assumes
    "dense_below(
    {q'\<in>\<bbbP>. \<forall>q. q\<in>\<bbbP> \<and> q\<preceq>q' \<longrightarrow> q forces\<^sub>a (s \<in> t1) \<longleftrightarrow> q forces\<^sub>a (s \<in> t2)}
    ,p)"
    "q forces\<^sub>a (s \<in> t1)" "q\<in>\<bbbP>" "p\<in>\<bbbP>" "q\<preceq>p"
  shows
    "dense_below({r\<in>\<bbbP>. r forces\<^sub>a (s \<in> t2)},q)"
proof
  fix r
  assume "r\<in>\<bbbP>" "r\<preceq>q"
  moreover from this and \<open>p\<in>\<bbbP>\<close> \<open>q\<preceq>p\<close> \<open>q\<in>\<bbbP>\<close>
  have "r\<preceq>p"
    using leq_transD by simp
  moreover
  note \<open>q forces\<^sub>a (s \<in> t1)\<close> \<open>dense_below(_,p)\<close> \<open>q\<in>\<bbbP>\<close>
  ultimately
  obtain q1 where "q1\<preceq>r" "q1\<in>\<bbbP>" "q1 forces\<^sub>a (s \<in> t2)"
    using strengthening_mem[of q _ s t1] refl_leq leq_transD[of _ r q] by blast
  then
  show "\<exists>d\<in>{r \<in> \<bbbP> . r forces\<^sub>a ( s \<in>  t2)}. d \<in> \<bbbP> \<and> d\<preceq> r"
    by blast
qed

(* Kunen 2013, Lemma IV.2.37(b) *)
lemma density_eq:
  assumes "p\<in>\<bbbP>"
  shows "p forces\<^sub>a (t1 = t2)  \<longleftrightarrow> dense_below({q\<in>\<bbbP>. q forces\<^sub>a (t1 = t2)},p)"
proof
  assume "p forces\<^sub>a (t1 = t2)"
  with \<open>p\<in>\<bbbP>\<close>
  show "dense_below({q\<in>\<bbbP>. q forces\<^sub>a (t1 = t2)},p)"
    using strengthening_eq ideal_dense_below by auto
next
  assume "dense_below({q\<in>\<bbbP>. q forces\<^sub>a (t1 = t2)},p)"
  {
    fix s q
    let ?D1="{q'\<in>\<bbbP>. \<forall>s\<in>domain(t1) \<union> domain(t2). \<forall>q. q \<in> \<bbbP> \<and> q\<preceq>q' \<longrightarrow>
           q forces\<^sub>a (s \<in> t1)\<longleftrightarrow>q forces\<^sub>a (s \<in> t2)}"
    let ?D2="{q'\<in>\<bbbP>. \<forall>q. q\<in>\<bbbP> \<and> q\<preceq>q' \<longrightarrow> q forces\<^sub>a (s \<in> t1) \<longleftrightarrow> q forces\<^sub>a (s \<in> t2)}"
    assume "s\<in>domain(t1) \<union> domain(t2)"
    then
    have "?D1\<subseteq>?D2" by blast
    with \<open>dense_below(_,p)\<close>
    have "dense_below({q'\<in>\<bbbP>. \<forall>s\<in>domain(t1) \<union> domain(t2). \<forall>q. q \<in> \<bbbP> \<and> q\<preceq>q' \<longrightarrow>
           q forces\<^sub>a (s \<in> t1)\<longleftrightarrow>q forces\<^sub>a (s \<in> t2)},p)"
      using dense_below_cong'[OF \<open>p\<in>\<bbbP>\<close> def_forces_eq[of _ t1 t2]] by simp
    with \<open>p\<in>\<bbbP>\<close> \<open>?D1\<subseteq>?D2\<close>
    have "dense_below({q'\<in>\<bbbP>. \<forall>q. q\<in>\<bbbP> \<and> q\<preceq>q' \<longrightarrow>
            q forces\<^sub>a (s \<in> t1) \<longleftrightarrow> q forces\<^sub>a (s \<in> t2)},p)"
      using dense_below_mono by simp
    moreover from this (* Automatic tools can't handle this symmetry
                          in order to apply aux_density_eq below *)
    have  "dense_below({q'\<in>\<bbbP>. \<forall>q. q\<in>\<bbbP> \<and> q\<preceq>q' \<longrightarrow>
            q forces\<^sub>a (s \<in> t2) \<longleftrightarrow> q forces\<^sub>a (s \<in> t1)},p)"
      by blast
    moreover
    assume "q \<in> \<bbbP>" "q\<preceq>p"
    moreover
    note \<open>p\<in>\<bbbP>\<close>
    ultimately (*We can omit the next step but it is slower *)
    have "q forces\<^sub>a (s \<in> t1) \<Longrightarrow> dense_below({r\<in>\<bbbP>. r forces\<^sub>a (s \<in> t2)},q)"
      "q forces\<^sub>a (s \<in> t2) \<Longrightarrow> dense_below({r\<in>\<bbbP>. r forces\<^sub>a (s \<in> t1)},q)"
      using aux_density_eq by simp_all
    then
    have "q forces\<^sub>a ( s \<in>  t1) \<longleftrightarrow> q forces\<^sub>a ( s \<in>  t2)"
      using density_mem[OF \<open>q\<in>\<bbbP>\<close>] by blast
  }
  with \<open>p\<in>\<bbbP>\<close>
  show "p forces\<^sub>a (t1 = t2)" using def_forces_eq by blast
qed

subsection\<open>Kunen 2013, Lemma IV.2.38\<close>
lemma not_forces_neq:
  assumes "p\<in>\<bbbP>"
  shows "p forces\<^sub>a (t1 = t2) \<longleftrightarrow> \<not> (\<exists>q\<in>\<bbbP>. q\<preceq>p \<and> q forces\<^sub>a (t1 \<noteq> t2))"
  using assms density_eq unfolding forces_neq_def by blast

lemma not_forces_nmem:
  assumes "p\<in>\<bbbP>"
  shows "p forces\<^sub>a (t1 \<in> t2) \<longleftrightarrow> \<not> (\<exists>q\<in>\<bbbP>. q\<preceq>p \<and> q forces\<^sub>a (t1 \<notin> t2))"
  using assms density_mem unfolding forces_nmem_def by blast

subsection\<open>The relation of forcing and atomic formulas\<close>
lemma Forces_Equal:
  assumes
    "p\<in>\<bbbP>" "t1\<in>M" "t2\<in>M" "env\<in>list(M)" "nth(n,env) = t1" "nth(m,env) = t2" "n\<in>nat" "m\<in>nat"
  shows
    "(p \<tturnstile> Equal(n,m) env) \<longleftrightarrow> p forces\<^sub>a (t1 = t2)"
  using assms sats_forces_Equal forces_eq_abs transitivity
  by simp

lemma Forces_Member:
  assumes
    "p\<in>\<bbbP>" "t1\<in>M" "t2\<in>M" "env\<in>list(M)" "nth(n,env) = t1" "nth(m,env) = t2" "n\<in>nat" "m\<in>nat"
  shows
    "(p \<tturnstile> Member(n,m) env) \<longleftrightarrow> p forces\<^sub>a (t1 \<in> t2)"
  using assms sats_forces_Member forces_mem_abs transitivity
  by simp

lemma Forces_Neg:
  assumes
    "p\<in>\<bbbP>" "env \<in> list(M)" "\<phi>\<in>formula"
  shows
    "(p \<tturnstile> Neg(\<phi>) env) \<longleftrightarrow> \<not>(\<exists>q\<in>M. q\<in>\<bbbP> \<and> q\<preceq>p \<and> (q \<tturnstile> \<phi> env))"
  using assms sats_forces_Neg transitivity pair_in_M_iff leq_abs
  by simp

subsection\<open>The relation of forcing and connectives\<close>

lemma Forces_Nand:
  assumes
    "p\<in>\<bbbP>" "env \<in> list(M)" "\<phi>\<in>formula" "\<psi>\<in>formula"
  shows
    "(p \<tturnstile> Nand(\<phi>,\<psi>) env) \<longleftrightarrow> \<not>(\<exists>q\<in>M. q\<in>\<bbbP> \<and> q\<preceq>p \<and> (q \<tturnstile> \<phi> env) \<and> (q \<tturnstile> \<psi> env))"
  using assms sats_forces_Nand transitivity pair_in_M_iff leq_abs by simp

lemma Forces_And_aux:
  assumes
    "p\<in>\<bbbP>" "env \<in> list(M)" "\<phi>\<in>formula" "\<psi>\<in>formula"
  shows
    "p \<tturnstile> And(\<phi>,\<psi>) env   \<longleftrightarrow>
    (\<forall>q\<in>M. q\<in>\<bbbP> \<and> q\<preceq>p \<longrightarrow> (\<exists>r\<in>M. r\<in>\<bbbP> \<and> r\<preceq>q \<and> (r \<tturnstile> \<phi> env) \<and> (r \<tturnstile> \<psi> env)))"
  unfolding And_def using assms Forces_Neg Forces_Nand by (auto simp only:)

lemma Forces_And_iff_dense_below:
  assumes
    "p\<in>\<bbbP>" "env \<in> list(M)" "\<phi>\<in>formula" "\<psi>\<in>formula"
  shows
    "(p \<tturnstile> And(\<phi>,\<psi>) env) \<longleftrightarrow> dense_below({r\<in>\<bbbP>. (r \<tturnstile> \<phi> env) \<and> (r \<tturnstile> \<psi> env) },p)"
  unfolding dense_below_def using Forces_And_aux assms
  by (auto dest:transitivity[OF _ P_in_M]; rename_tac q; drule_tac x=q in bspec)+

lemma Forces_Forall:
  assumes
    "p\<in>\<bbbP>" "env \<in> list(M)" "\<phi>\<in>formula"
  shows
    "(p \<tturnstile> Forall(\<phi>) env) \<longleftrightarrow> (\<forall>x\<in>M. (p \<tturnstile> \<phi> ([x] @ env)))"
  using sats_forces_Forall assms transitivity[OF _ P_in_M]
  by simp

(* "x\<in>val(G,\<pi>) \<Longrightarrow> \<exists>\<theta>. \<exists>p\<in>G.  \<langle>\<theta>,p\<rangle>\<in>\<pi> \<and> val(G,\<theta>) = x" *)
bundle some_rules =  elem_of_val_pair [dest]

context
  includes some_rules
begin

lemma elem_of_valI: "\<exists>\<theta>. \<exists>p\<in>\<bbbP>. p\<in>G \<and> \<langle>\<theta>,p\<rangle>\<in>\<pi> \<and> val(G,\<theta>) = x \<Longrightarrow> x\<in>val(G,\<pi>)"
  by (subst def_val, auto)

lemma GenExt_iff: "x\<in>M[G] \<longleftrightarrow> (\<exists>\<tau>\<in>M. x = val(G,\<tau>))"
  unfolding GenExt_def by simp
end

end
context G_generic1
  
begin

subsection\<open>Kunen 2013, Lemma IV.2.29\<close>
lemma generic_inter_dense_below:
  assumes "D\<in>M" "dense_below(D,p)" "p\<in>G"
  shows "D \<inter> G \<noteq> 0"
proof -
  let ?D="{q\<in>\<bbbP>. p\<bottom>q \<or> q\<in>D}"
  have "dense(?D)"
  proof
    fix r
    assume "r\<in>\<bbbP>"
    show "\<exists>d\<in>{q \<in> \<bbbP> . p \<bottom> q \<or> q \<in> D}. d \<preceq> r"
    proof (cases "p \<bottom> r")
      case True
      with \<open>r\<in>\<bbbP>\<close>
        (* Automatic tools can't handle this case for some reason... *)
      show ?thesis using refl_leq[of r] by (intro bexI) (blast+)
    next
      case False
      then
      obtain s where "s\<in>\<bbbP>" "s\<preceq>p" "s\<preceq>r" by blast
      with assms \<open>r\<in>\<bbbP>\<close>
      show ?thesis
        using dense_belowD[OF assms(2), of s] leq_transD[of _ s r]
        by blast
    qed
  qed
  have "?D\<subseteq>\<bbbP>" by auto
  let ?d_fm="\<cdot>\<cdot>\<not>compat_in_fm(1, 2, 3, 0) \<cdot> \<or> \<cdot>0 \<in> 4\<cdot>\<cdot>"
  from \<open>p\<in>G\<close>
  have "p\<in>M"
    using G_subset_M subsetD by simp
  moreover
  have "?d_fm\<in>formula" by simp
  moreover
  have "arity(?d_fm) = 5"
    by (auto simp add: arity)
  moreover from \<open>D\<in>M\<close> \<open>p\<in>M\<close>
  have "(M, [q,\<bbbP>,leq,p,D] \<Turnstile> ?d_fm) \<longleftrightarrow> (\<not> is_compat_in(##M,\<bbbP>,leq,p,q) \<or> q\<in>D)"
    if "q\<in>M" for q
    using that sats_compat_in_fm zero_in_M
    by simp
  moreover from \<open>p\<in>M\<close>
  have "(\<not> is_compat_in(##M,\<bbbP>,leq,p,q) \<or> q\<in>D) \<longleftrightarrow> p\<bottom>q \<or> q\<in>D" if "q\<in>M" for q
    unfolding compat_def
    using that compat_in_abs
    by simp
  ultimately
  have "?D\<in>M"
    using Collect_in_M[of ?d_fm "[\<bbbP>,leq,p,D]"] \<open>D\<in>M\<close>
    by simp
  note asm = \<open>dense(?D)\<close> \<open>?D\<subseteq>\<bbbP>\<close> \<open>?D\<in>M\<close>
  obtain x where "x\<in>G" "x\<in>?D" 
    using M_generic_denseD[OF asm]
    by force (* by (erule bexE) does it, but the other automatic tools don't *)
  moreover from this
  have "x\<in>D"
    using M_generic_compatD[OF _ \<open>p\<in>G\<close>, of x] refl_leq compatI[of _ p x]
    by force
  ultimately
  show ?thesis by auto
qed

subsection\<open>Auxiliary results for Lemma IV.2.40(a)\<close>
lemma (in forcing_data1) IV240a_mem_Collect:
  assumes
    "\<pi>\<in>M" "\<tau>\<in>M"
  shows
    "{q\<in>\<bbbP>. \<exists>\<sigma>. \<exists>r. r\<in>\<bbbP> \<and> \<langle>\<sigma>,r\<rangle> \<in> \<tau> \<and> q\<preceq>r \<and> q forces\<^sub>a (\<pi> = \<sigma>)}\<in>M"
proof -
  let ?rel_pred= "\<lambda>M x a1 a2 a3 a4. \<exists>\<sigma>[M]. \<exists>r[M]. \<exists>\<sigma>r[M].
                r\<in>a1 \<and> pair(M,\<sigma>,r,\<sigma>r) \<and> \<sigma>r\<in>a4 \<and> is_leq(M,a2,x,r) \<and> is_forces_eq'(M,a1,a2,x,a3,\<sigma>)"
  let ?\<phi>="Exists(Exists(Exists(And(Member(1,4),And(pair_fm(2,1,0),
          And(Member(0,7),And(is_leq_fm(5,3,1),forces_eq_fm(4,5,3,6,2))))))))"
  have "\<sigma>\<in>M \<and> r\<in>M" if "\<langle>\<sigma>, r\<rangle> \<in> \<tau>"  for \<sigma> r
    using that \<open>\<tau>\<in>M\<close> pair_in_M_iff transitivity[of "\<langle>\<sigma>,r\<rangle>" \<tau>] by simp
  then
  have "?rel_pred(##M,q,\<bbbP>,leq,\<pi>,\<tau>) \<longleftrightarrow> (\<exists>\<sigma>. \<exists>r. r\<in>\<bbbP> \<and> \<langle>\<sigma>,r\<rangle> \<in> \<tau> \<and> q\<preceq>r \<and> q forces\<^sub>a (\<pi> = \<sigma>))"
    if "q\<in>M" for q
    unfolding forces_eq_def
    using assms that leq_abs forces_eq'_abs pair_in_M_iff
    by auto
  moreover
  have "(M, [q,\<bbbP>,leq,\<pi>,\<tau>] \<Turnstile> ?\<phi>) \<longleftrightarrow> ?rel_pred(##M,q,\<bbbP>,leq,\<pi>,\<tau>)" if "q\<in>M" for q
    using assms that sats_forces_eq_fm sats_is_leq_fm zero_in_M
    by simp
  moreover
  have "?\<phi>\<in>formula" by simp
  moreover
  have "arity(?\<phi>)=5"
    using arity_forces_eq_fm
    by (simp add:ord_simp_union arity)
  ultimately
  show ?thesis
    unfolding forces_eq_def using assms Collect_in_M[of ?\<phi> "[\<bbbP>,leq,\<pi>,\<tau>]"]
    by simp
qed

(* Lemma IV.2.40(a), membership *)
lemma IV240a_mem:
  assumes
    "p\<in>G" "\<pi>\<in>M" "\<tau>\<in>M" "p forces\<^sub>a (\<pi> \<in> \<tau>)"
    "\<And>q \<sigma>. q\<in>\<bbbP> \<Longrightarrow> q\<in>G \<Longrightarrow> \<sigma>\<in>domain(\<tau>) \<Longrightarrow> q forces\<^sub>a (\<pi> = \<sigma>) \<Longrightarrow>
      val(G,\<pi>) = val(G,\<sigma>)" (* inductive hypothesis *)
  shows
    "val(G,\<pi>)\<in>val(G,\<tau>)"
proof (intro elem_of_valI)
  let ?D="{q\<in>\<bbbP>. \<exists>\<sigma>. \<exists>r. r\<in>\<bbbP> \<and> \<langle>\<sigma>,r\<rangle> \<in> \<tau> \<and> q\<preceq>r \<and> q forces\<^sub>a (\<pi> = \<sigma>)}"
  from \<open>p\<in>G\<close>
  have "p\<in>\<bbbP>" by blast
  moreover
  note \<open>\<pi>\<in>M\<close> \<open>\<tau>\<in>M\<close>
  ultimately
  have "?D \<in> M" using IV240a_mem_Collect by simp
  moreover from assms \<open>p\<in>\<bbbP>\<close>
  have "dense_below(?D,p)"
    using forces_mem_iff_dense_below by simp
  moreover
  note \<open>p\<in>G\<close>
  ultimately
  obtain q where "q\<in>G" "q\<in>?D" 
    using generic_inter_dense_below[of ?D p] by blast
  then
  obtain \<sigma> r where "r\<in>\<bbbP>" "\<langle>\<sigma>,r\<rangle> \<in> \<tau>" "q\<preceq>r" "q forces\<^sub>a (\<pi> = \<sigma>)" by blast
  moreover from this and \<open>q\<in>G\<close> assms
  have "r \<in> G" "val(G,\<pi>) = val(G,\<sigma>)" by blast+
  ultimately
  show "\<exists> \<sigma>. \<exists>p\<in>\<bbbP>. p \<in> G \<and> \<langle>\<sigma>, p\<rangle> \<in> \<tau> \<and> val(G, \<sigma>) = val(G, \<pi>)" by auto
qed

(* Example IV.2.36 (next two lemmas) *)
lemma refl_forces_eq:"p\<in>\<bbbP> \<Longrightarrow> p forces\<^sub>a (x = x)"
  using def_forces_eq by simp

lemma forces_memI: "\<langle>\<sigma>,r\<rangle>\<in>\<tau> \<Longrightarrow> p\<in>\<bbbP> \<Longrightarrow> r\<in>\<bbbP> \<Longrightarrow> p\<preceq>r \<Longrightarrow> p forces\<^sub>a (\<sigma> \<in> \<tau>)"
  using refl_forces_eq[of _ \<sigma>] leq_transD refl_leq
  by (blast intro:forces_mem_iff_dense_below[THEN iffD2])

(* Lemma IV.2.40(a), equality, first inclusion *)
lemma IV240a_eq_1st_incl:
  includes some_rules
  assumes
    "p\<in>G" "p forces\<^sub>a (\<tau> = \<theta>)"
    and
    IH:"\<And>q \<sigma>. q\<in>\<bbbP> \<Longrightarrow> q\<in>G \<Longrightarrow> \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow>
        (q forces\<^sub>a (\<sigma> \<in> \<tau>) \<longrightarrow> val(G,\<sigma>) \<in> val(G,\<tau>)) \<and>
        (q forces\<^sub>a (\<sigma> \<in> \<theta>) \<longrightarrow> val(G,\<sigma>) \<in> val(G,\<theta>))"
    (* Strong enough for this case: *)
    (*  IH:"\<And>q \<sigma>. q\<in>\<bbbP> \<Longrightarrow> \<sigma>\<in>domain(\<tau>) \<Longrightarrow> q forces\<^sub>a (\<sigma> \<in> \<theta>) \<Longrightarrow>
      val(G,\<sigma>) \<in> val(G,\<theta>)" *)
  shows
    "val(G,\<tau>) \<subseteq> val(G,\<theta>)"
proof
  fix x
  assume "x\<in>val(G,\<tau>)"
  then
  obtain \<sigma> r where "\<langle>\<sigma>,r\<rangle>\<in>\<tau>" "r\<in>G" "val(G,\<sigma>)=x" by blast
  moreover from this and \<open>p\<in>G\<close>
  obtain q where "q\<in>G" "q\<preceq>p" "q\<preceq>r" by force
  moreover from this and \<open>p\<in>G\<close>
  have "q\<in>\<bbbP>" "p\<in>\<bbbP>" by blast+
  moreover from calculation
  have "q forces\<^sub>a (\<sigma> \<in> \<tau>)"
    using forces_memI by auto
  moreover
  note \<open>p forces\<^sub>a (\<tau> = \<theta>)\<close>
  ultimately
  have "q forces\<^sub>a (\<sigma> \<in> \<theta>)"
    using def_forces_eq by auto
  with \<open>q\<in>\<bbbP>\<close> \<open>q\<in>G\<close> IH[of q \<sigma>] \<open>\<langle>\<sigma>,r\<rangle>\<in>\<tau>\<close> \<open>val(G,\<sigma>) = x\<close>
  show "x\<in>val(G,\<theta>)" by blast
qed

(* Lemma IV.2.40(a), equality, second inclusion--- CO\<bbbP>Y-\<bbbP>ASTE *)
lemma IV240a_eq_2nd_incl:
  includes some_rules
  assumes
    "p\<in>G" "p forces\<^sub>a (\<tau> = \<theta>)"
    and
    IH:"\<And>q \<sigma>. q\<in>\<bbbP> \<Longrightarrow> q\<in>G \<Longrightarrow> \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow>
        (q forces\<^sub>a (\<sigma> \<in> \<tau>) \<longrightarrow> val(G,\<sigma>) \<in> val(G,\<tau>)) \<and>
        (q forces\<^sub>a (\<sigma> \<in> \<theta>) \<longrightarrow> val(G,\<sigma>) \<in> val(G,\<theta>))"
  shows
    "val(G,\<theta>) \<subseteq> val(G,\<tau>)"
proof
  fix x
  assume "x\<in>val(G,\<theta>)"
  then
  obtain \<sigma> r where "\<langle>\<sigma>,r\<rangle>\<in>\<theta>" "r\<in>G" "val(G,\<sigma>)=x" by blast
  moreover from this and \<open>p\<in>G\<close>
  obtain q where "q\<in>G" "q\<preceq>p" "q\<preceq>r" by force
  moreover from this and \<open>p\<in>G\<close>
  have "q\<in>\<bbbP>" "p\<in>\<bbbP>" by blast+
  moreover from calculation
  have "q forces\<^sub>a (\<sigma> \<in> \<theta>)"
    using forces_memI by auto
  moreover
  note \<open>p forces\<^sub>a (\<tau> = \<theta>)\<close>
  ultimately
  have "q forces\<^sub>a (\<sigma> \<in> \<tau>)"
    using def_forces_eq by auto
  with \<open>q\<in>\<bbbP>\<close> \<open>q\<in>G\<close> IH[of q \<sigma>] \<open>\<langle>\<sigma>,r\<rangle>\<in>\<theta>\<close> \<open>val(G,\<sigma>) = x\<close>
  show "x\<in>val(G,\<tau>)" by blast
qed

(* Lemma IV.2.40(a), equality, second inclusion--- CO\<bbbP>Y-\<bbbP>ASTE *)
lemma IV240a_eq:
  includes some_rules
  assumes
    "p\<in>G" "p forces\<^sub>a (\<tau> = \<theta>)"
    and
    IH:"\<And>q \<sigma>. q\<in>\<bbbP> \<Longrightarrow> q\<in>G \<Longrightarrow> \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow>
        (q forces\<^sub>a (\<sigma> \<in> \<tau>) \<longrightarrow> val(G,\<sigma>) \<in> val(G,\<tau>)) \<and>
        (q forces\<^sub>a (\<sigma> \<in> \<theta>) \<longrightarrow> val(G,\<sigma>) \<in> val(G,\<theta>))"
  shows
    "val(G,\<tau>) = val(G,\<theta>)"
  using IV240a_eq_1st_incl[OF assms] IV240a_eq_2nd_incl[OF assms] IH by blast

subsection\<open>Induction on names\<close>

lemma (in forcing_data1) core_induction:
  assumes
    "\<And>\<tau> \<theta> p. p \<in> \<bbbP> \<Longrightarrow> \<lbrakk>\<And>q \<sigma>. \<lbrakk>q\<in>\<bbbP> ; \<sigma>\<in>domain(\<theta>)\<rbrakk> \<Longrightarrow> Q(0,\<tau>,\<sigma>,q)\<rbrakk> \<Longrightarrow> Q(1,\<tau>,\<theta>,p)"
    "\<And>\<tau> \<theta> p. p \<in> \<bbbP> \<Longrightarrow> \<lbrakk>\<And>q \<sigma>. \<lbrakk>q\<in>\<bbbP> ; \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>)\<rbrakk> \<Longrightarrow> Q(1,\<sigma>,\<tau>,q) \<and> Q(1,\<sigma>,\<theta>,q)\<rbrakk> \<Longrightarrow> Q(0,\<tau>,\<theta>,p)"
    "ft \<in> 2" "p \<in> \<bbbP>"
  shows
    "Q(ft,\<tau>,\<theta>,p)"
proof -
  {
    fix ft p \<tau> \<theta>
    have "Transset(eclose({\<tau>,\<theta>}))" (is "Transset(?e)")
      using Transset_eclose by simp
    have "\<tau> \<in> ?e" "\<theta> \<in> ?e"
      using arg_into_eclose by simp_all
    moreover
    assume "ft \<in> 2" "p \<in> \<bbbP>"
    ultimately
    have "\<langle>ft,\<tau>,\<theta>,p\<rangle>\<in> 2\<times>?e\<times>?e\<times>\<bbbP>" (is "?a\<in>2\<times>?e\<times>?e\<times>\<bbbP>") by simp
    then
    have "Q(ftype(?a), name1(?a), name2(?a), cond_of(?a))"
      using core_induction_aux[of ?e \<bbbP> Q ?a,OF \<open>Transset(?e)\<close> assms(1,2) \<open>?a\<in>_\<close>]
      by (clarify) (blast)
    then have "Q(ft,\<tau>,\<theta>,p)" by (simp add:components_simp)
  }
  then show ?thesis using assms by simp
qed

lemma (in forcing_data1) forces_induction_with_conds:
  assumes
    "\<And>\<tau> \<theta> p. p \<in> \<bbbP> \<Longrightarrow> \<lbrakk>\<And>q \<sigma>. \<lbrakk>q\<in>\<bbbP> ; \<sigma>\<in>domain(\<theta>)\<rbrakk> \<Longrightarrow> Q(q,\<tau>,\<sigma>)\<rbrakk> \<Longrightarrow> R(p,\<tau>,\<theta>)"
    "\<And>\<tau> \<theta> p. p \<in> \<bbbP> \<Longrightarrow> \<lbrakk>\<And>q \<sigma>. \<lbrakk>q\<in>\<bbbP> ; \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>)\<rbrakk> \<Longrightarrow> R(q,\<sigma>,\<tau>) \<and> R(q,\<sigma>,\<theta>)\<rbrakk> \<Longrightarrow> Q(p,\<tau>,\<theta>)"
    "p \<in> \<bbbP>"
  shows
    "Q(p,\<tau>,\<theta>) \<and> R(p,\<tau>,\<theta>)"
proof -
  let ?Q="\<lambda>ft \<tau> \<theta> p. (ft = 0 \<longrightarrow> Q(p,\<tau>,\<theta>)) \<and> (ft = 1 \<longrightarrow> R(p,\<tau>,\<theta>))"
  from assms(1)
  have "\<And>\<tau> \<theta> p. p \<in> \<bbbP> \<Longrightarrow> \<lbrakk>\<And>q \<sigma>. \<lbrakk>q\<in>\<bbbP> ; \<sigma>\<in>domain(\<theta>)\<rbrakk> \<Longrightarrow> ?Q(0,\<tau>,\<sigma>,q)\<rbrakk> \<Longrightarrow> ?Q(1,\<tau>,\<theta>,p)"
    by simp
  moreover from assms(2)
  have "\<And>\<tau> \<theta> p. p \<in> \<bbbP> \<Longrightarrow> \<lbrakk>\<And>q \<sigma>. \<lbrakk>q\<in>\<bbbP> ; \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>)\<rbrakk> \<Longrightarrow> ?Q(1,\<sigma>,\<tau>,q) \<and> ?Q(1,\<sigma>,\<theta>,q)\<rbrakk> \<Longrightarrow> ?Q(0,\<tau>,\<theta>,p)"
    by simp
  moreover
  note \<open>p\<in>\<bbbP>\<close>
  ultimately
  have "?Q(ft,\<tau>,\<theta>,p)" if "ft\<in>2" for ft
    by (rule core_induction[OF _ _ that, of ?Q])
  then
  show ?thesis by auto
qed

lemma (in forcing_data1) forces_induction:
  assumes
    "\<And>\<tau> \<theta>. \<lbrakk>\<And>\<sigma>. \<sigma>\<in>domain(\<theta>) \<Longrightarrow> Q(\<tau>,\<sigma>)\<rbrakk> \<Longrightarrow> R(\<tau>,\<theta>)"
    "\<And>\<tau> \<theta>. \<lbrakk>\<And>\<sigma>. \<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow> R(\<sigma>,\<tau>) \<and> R(\<sigma>,\<theta>)\<rbrakk> \<Longrightarrow> Q(\<tau>,\<theta>)"
  shows
    "Q(\<tau>,\<theta>) \<and> R(\<tau>,\<theta>)"
proof (intro forces_induction_with_conds[OF _ _ one_in_P ])
  fix \<tau> \<theta> p
  assume "q \<in> \<bbbP> \<Longrightarrow> \<sigma> \<in> domain(\<theta>) \<Longrightarrow> Q(\<tau>, \<sigma>)" for q \<sigma>
  with assms(1)
  show "R(\<tau>,\<theta>)"
    using one_in_P by simp
next
  fix \<tau> \<theta> p
  assume "q \<in> \<bbbP> \<Longrightarrow> \<sigma> \<in> domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow> R(\<sigma>,\<tau>) \<and> R(\<sigma>,\<theta>)" for q \<sigma>
  with assms(2)
  show "Q(\<tau>,\<theta>)"
    using one_in_P by simp
qed

subsection\<open>Lemma IV.2.40(a), in full\<close>
lemma IV240a:
  shows
    "(\<tau>\<in>M \<longrightarrow> \<theta>\<in>M \<longrightarrow> (\<forall>p\<in>G. p forces\<^sub>a (\<tau> = \<theta>) \<longrightarrow> val(G,\<tau>) = val(G,\<theta>))) \<and>
     (\<tau>\<in>M \<longrightarrow> \<theta>\<in>M \<longrightarrow> (\<forall>p\<in>G. p forces\<^sub>a (\<tau> \<in> \<theta>) \<longrightarrow> val(G,\<tau>) \<in> val(G,\<theta>)))"
    (is "?Q(\<tau>,\<theta>) \<and> ?R(\<tau>,\<theta>)")
proof (intro forces_induction[of ?Q ?R] impI)
  fix \<tau> \<theta>
  assume "\<tau>\<in>M" "\<theta>\<in>M"  "\<sigma>\<in>domain(\<theta>) \<Longrightarrow> ?Q(\<tau>,\<sigma>)" for \<sigma>
  moreover from this
  have "\<sigma>\<in>domain(\<theta>) \<Longrightarrow> q forces\<^sub>a (\<tau> = \<sigma>) \<Longrightarrow> val(G, \<tau>) = val(G, \<sigma>)"
    if "q\<in>\<bbbP>" "q\<in>G" for q \<sigma>
    using that domain_closed[of \<theta>] transitivity by auto
  ultimately
  show "\<forall>p\<in>G. p forces\<^sub>a (\<tau> \<in> \<theta>) \<longrightarrow> val(G,\<tau>) \<in> val(G,\<theta>)"
    using IV240a_mem domain_closed transitivity by simp
next
  fix \<tau> \<theta>
  assume "\<tau>\<in>M" "\<theta>\<in>M" and d:"\<sigma> \<in> domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow> ?R(\<sigma>,\<tau>) \<and> ?R(\<sigma>,\<theta>)" for \<sigma>
  moreover from this
  have IH':"(q forces\<^sub>a (\<sigma> \<in> \<tau>) \<longrightarrow> val(G, \<sigma>) \<in> val(G, \<tau>)) \<and>
            (q forces\<^sub>a (\<sigma> \<in> \<theta>) \<longrightarrow> val(G, \<sigma>) \<in> val(G, \<theta>))" 
    if "\<sigma> \<in> domain(\<tau>) \<union> domain(\<theta>)" "q\<in>G" for q \<sigma>
  proof -
    from d that
    have A:"?R(\<sigma>,\<tau>)" "?R(\<sigma>,\<theta>)"
      by auto
    from \<open>\<tau>\<in>_\<close> \<open>\<theta>\<in>M\<close> \<open>q\<in>G\<close> \<open>\<sigma>\<in>_\<close>
     show ?thesis
      using transitivity[of \<sigma>] domain_closed A[rule_format,of q]
      by auto
  qed
  show "\<forall>p\<in>G. p forces\<^sub>a (\<tau> = \<theta>) \<longrightarrow> val(G,\<tau>) = val(G,\<theta>)"
    using IV240a_eq[OF _ _ IH'] by simp
qed

subsection\<open>Lemma IV.2.40(b)\<close>
  (* Lemma IV.2.40(b), membership *)
lemma IV240b_mem:
  includes some_rules
  assumes
    "val(G,\<pi>)\<in>val(G,\<tau>)" "\<pi>\<in>M" "\<tau>\<in>M"
    and
    IH:"\<And>\<sigma>. \<sigma>\<in>domain(\<tau>) \<Longrightarrow> val(G,\<pi>) = val(G,\<sigma>) \<Longrightarrow>
      \<exists>p\<in>G. p forces\<^sub>a (\<pi> = \<sigma>)" (* inductive hypothesis *)
  shows
    "\<exists>p\<in>G. p forces\<^sub>a (\<pi> \<in> \<tau>)"
proof -
  from \<open>val(G,\<pi>)\<in>val(G,\<tau>)\<close>
  obtain \<sigma> r where "r\<in>G" "\<langle>\<sigma>,r\<rangle>\<in>\<tau>" "val(G,\<pi>) = val(G,\<sigma>)" by auto
  moreover from this and IH
  obtain p' where "p'\<in>G" "p' forces\<^sub>a (\<pi> = \<sigma>)" by blast
  ultimately
  obtain p where "p\<preceq>r" "p\<preceq>p'" "p\<in>G" "p forces\<^sub>a (\<pi> = \<sigma>)"
    using M_generic_compatD strengthening_eq[of p'] M_genericD by auto
  moreover from calculation
  have "q forces\<^sub>a (\<pi> = \<sigma>)" if "q\<in>\<bbbP>" "q\<preceq>p" for q
    using that strengthening_eq by blast
  moreover
  note \<open>\<langle>\<sigma>,r\<rangle>\<in>\<tau>\<close> \<open>r\<in>G\<close>
  ultimately
  have "r\<in>\<bbbP> \<and> \<langle>\<sigma>,r\<rangle> \<in> \<tau> \<and> q\<preceq>r \<and> q forces\<^sub>a (\<pi> = \<sigma>)" if "q\<in>\<bbbP>" "q\<preceq>p" for q
    using that leq_transD[of _ p r] by blast
  then
  have "dense_below({q\<in>\<bbbP>. \<exists>s r. r\<in>\<bbbP> \<and> \<langle>s,r\<rangle> \<in> \<tau> \<and> q\<preceq>r \<and> q forces\<^sub>a (\<pi> = s)},p)"
    using refl_leq by blast
  moreover
  note \<open>p\<in>G\<close>
  moreover from calculation
  have "p forces\<^sub>a (\<pi> \<in> \<tau>)"
    using forces_mem_iff_dense_below by blast
  ultimately
  show ?thesis by blast
qed

end \<comment> \<open>\<^locale>\<open>G_generic1\<close>\<close>

context forcing_data1
begin

lemma Collect_forces_eq_in_M:
  assumes "\<tau> \<in> M" "\<theta> \<in> M"
  shows "{p\<in>\<bbbP>. p forces\<^sub>a (\<tau> = \<theta>)} \<in> M"
  using assms Collect_in_M[of "forces_eq_fm(1,2,0,3,4)" "[\<bbbP>,leq,\<tau>,\<theta>]"]
    arity_forces_eq_fm sats_forces_eq_fm forces_eq_abs forces_eq_fm_type
  by (simp add: union_abs1 Un_commute)

lemma IV240b_eq_Collects:
  assumes "\<tau> \<in> M" "\<theta> \<in> M"
  shows "{p\<in>\<bbbP>. \<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). p forces\<^sub>a (\<sigma> \<in> \<tau>) \<and> p forces\<^sub>a (\<sigma> \<notin> \<theta>)}\<in>M" and
    "{p\<in>\<bbbP>. \<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). p forces\<^sub>a (\<sigma> \<notin> \<tau>) \<and> p forces\<^sub>a (\<sigma> \<in> \<theta>)}\<in>M"
proof -
  let ?rel_pred="\<lambda>M x a1 a2 a3 a4.
        \<exists>\<sigma>[M]. \<exists>u[M]. \<exists>da3[M]. \<exists>da4[M]. is_domain(M,a3,da3) \<and> is_domain(M,a4,da4) \<and>
          union(M,da3,da4,u) \<and> \<sigma>\<in>u \<and> is_forces_mem'(M,a1,a2,x,\<sigma>,a3) \<and>
          is_forces_nmem'(M,a1,a2,x,\<sigma>,a4)"
  let ?\<phi>="Exists(Exists(Exists(Exists(And(domain_fm(7,1),And(domain_fm(8,0),
          And(union_fm(1,0,2),And(Member(3,2),And(forces_mem_fm(5,6,4,3,7),
                              forces_nmem_fm(5,6,4,3,8))))))))))"
  have 1:"\<sigma>\<in>M" if "\<langle>\<sigma>,y\<rangle>\<in>\<delta>" "\<delta>\<in>M" for \<sigma> \<delta> y
    using that pair_in_M_iff transitivity[of "\<langle>\<sigma>,y\<rangle>" \<delta>] by simp
  have abs1:"?rel_pred(##M,p,\<bbbP>,leq,\<tau>,\<theta>) \<longleftrightarrow>
        (\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). forces_mem'(\<bbbP>,leq,p,\<sigma>,\<tau>) \<and> forces_nmem'(\<bbbP>,leq,p,\<sigma>,\<theta>))"
    if "p\<in>M" for p
    unfolding forces_mem_def forces_nmem_def
    using assms that forces_mem'_abs forces_nmem'_abs
      domain_closed Un_closed
    by (auto simp add:1[of _ _ \<tau>] 1[of _ _ \<theta>])
  have abs2:"?rel_pred(##M,p,\<bbbP>,leq,\<theta>,\<tau>) \<longleftrightarrow> (\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>).
        forces_nmem'(\<bbbP>,leq,p,\<sigma>,\<tau>) \<and> forces_mem'(\<bbbP>,leq,p,\<sigma>,\<theta>))" if "p\<in>M" for p
    unfolding forces_mem_def forces_nmem_def
    using assms that forces_mem'_abs forces_nmem'_abs
      domain_closed Un_closed
    by (auto simp add:1[of _ _ \<tau>] 1[of _ _ \<theta>])
  have fsats1:"(M,[p,\<bbbP>,leq,\<tau>,\<theta>] \<Turnstile> ?\<phi>) \<longleftrightarrow> ?rel_pred(##M,p,\<bbbP>,leq,\<tau>,\<theta>)" if "p\<in>M" for p
    using that assms sats_forces_mem_fm sats_forces_nmem_fm zero_in_M
      domain_closed Un_closed by simp
  have fsats2:"(M,[p,\<bbbP>,leq,\<theta>,\<tau>] \<Turnstile> ?\<phi>) \<longleftrightarrow> ?rel_pred(##M,p,\<bbbP>,leq,\<theta>,\<tau>)" if "p\<in>M" for p
    using that assms sats_forces_mem_fm sats_forces_nmem_fm zero_in_M
      domain_closed Un_closed by simp
  have fty:"?\<phi>\<in>formula" by simp
  have farit:"arity(?\<phi>)=5"
    by (simp add:ord_simp_union arity)
  show
    "{p \<in> \<bbbP> . \<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). p forces\<^sub>a (\<sigma> \<in> \<tau>) \<and> p forces\<^sub>a (\<sigma> \<notin> \<theta>)} \<in> M"
    and "{p \<in> \<bbbP> . \<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). p forces\<^sub>a (\<sigma> \<notin> \<tau>) \<and> p forces\<^sub>a (\<sigma> \<in> \<theta>)} \<in> M"
    unfolding forces_mem_def
    using abs1 fty fsats1 farit assms forces_nmem
      Collect_in_M[of ?\<phi> "[\<bbbP>,leq,\<tau>,\<theta>]"]
    using abs2 fty fsats2 farit assms forces_nmem domain_closed Un_closed
      Collect_in_M[of ?\<phi> "[\<bbbP>,leq,\<theta>,\<tau>]"]
    by simp_all
qed

end \<comment> \<open>\<^locale>\<open>forcing_data1\<close>\<close>

context G_generic1
begin

(* Lemma IV.2.40(b), equality *)
lemma IV240b_eq:
  includes some_rules
  assumes
    "val(G,\<tau>) = val(G,\<theta>)" "\<tau>\<in>M" "\<theta>\<in>M"
    and
    IH:"\<And>\<sigma>. \<sigma>\<in>domain(\<tau>)\<union>domain(\<theta>) \<Longrightarrow>
      (val(G,\<sigma>)\<in>val(G,\<tau>) \<longrightarrow> (\<exists>q\<in>G. q forces\<^sub>a (\<sigma> \<in> \<tau>))) \<and>
      (val(G,\<sigma>)\<in>val(G,\<theta>) \<longrightarrow> (\<exists>q\<in>G. q forces\<^sub>a (\<sigma> \<in> \<theta>)))"
    (* inductive hypothesis *)
  shows
    "\<exists>p\<in>G. p forces\<^sub>a (\<tau> = \<theta>)"
proof -
  let ?D1="{p\<in>\<bbbP>. p forces\<^sub>a (\<tau> = \<theta>)}"
  let ?D2="{p\<in>\<bbbP>. \<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). p forces\<^sub>a (\<sigma> \<in> \<tau>) \<and> p forces\<^sub>a (\<sigma> \<notin> \<theta>)}"
  let ?D3="{p\<in>\<bbbP>. \<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). p forces\<^sub>a (\<sigma> \<notin> \<tau>) \<and> p forces\<^sub>a (\<sigma> \<in> \<theta>)}"
  let ?D="?D1 \<union> ?D2 \<union> ?D3"
  note assms
  moreover from this
  have "domain(\<tau>) \<union> domain(\<theta>)\<in>M" (is "?B\<in>M") using domain_closed Un_closed by auto
  moreover from calculation
  have "?D2\<in>M" and "?D3\<in>M" using IV240b_eq_Collects by simp_all
  ultimately
  have "?D\<in>M" using Collect_forces_eq_in_M Un_closed by auto
  moreover
  have "dense(?D)"
  proof
    fix p
    assume "p\<in>\<bbbP>"
    have "\<exists>d\<in>\<bbbP>. (d forces\<^sub>a (\<tau> = \<theta>) \<or>
            (\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). d forces\<^sub>a (\<sigma> \<in> \<tau>) \<and> d forces\<^sub>a (\<sigma> \<notin> \<theta>)) \<or>
            (\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). d forces\<^sub>a (\<sigma> \<notin> \<tau>) \<and> d forces\<^sub>a (\<sigma> \<in> \<theta>))) \<and>
           d \<preceq> p"
    proof (cases "p forces\<^sub>a (\<tau> = \<theta>)")
      case True
      with \<open>p\<in>\<bbbP>\<close>
      show ?thesis using refl_leq by blast
    next
      case False
      moreover note \<open>p\<in>\<bbbP>\<close>
      moreover from calculation
      obtain \<sigma> q where "\<sigma>\<in>domain(\<tau>)\<union>domain(\<theta>)" "q\<in>\<bbbP>" "q\<preceq>p"
        "(q forces\<^sub>a (\<sigma> \<in> \<tau>) \<and> \<not> q forces\<^sub>a (\<sigma> \<in> \<theta>)) \<or>
         (\<not> q forces\<^sub>a (\<sigma> \<in> \<tau>) \<and> q forces\<^sub>a (\<sigma> \<in> \<theta>))"
        using def_forces_eq by blast
      moreover from this
      obtain r where "r\<preceq>q" "r\<in>\<bbbP>"
        "(r forces\<^sub>a (\<sigma> \<in> \<tau>) \<and> r forces\<^sub>a (\<sigma> \<notin> \<theta>)) \<or>
         (r forces\<^sub>a (\<sigma> \<notin> \<tau>) \<and> r forces\<^sub>a (\<sigma> \<in> \<theta>))"
        using not_forces_nmem strengthening_mem by blast
      ultimately
      show ?thesis using leq_transD by blast
    qed
    then
    show "\<exists>d\<in>?D . d \<preceq> p" by blast
  qed
  moreover
  have "?D \<subseteq> \<bbbP>"
    by auto
  ultimately
  obtain p where "p\<in>G" "p\<in>?D"
    using M_generic_denseD[of ?D] by blast
  then
  consider
    (1) "p forces\<^sub>a (\<tau> = \<theta>)" |
    (2) "\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). p forces\<^sub>a (\<sigma> \<in> \<tau>) \<and> p forces\<^sub>a (\<sigma> \<notin> \<theta>)" |
    (3) "\<exists>\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>). p forces\<^sub>a (\<sigma> \<notin> \<tau>) \<and> p forces\<^sub>a (\<sigma> \<in> \<theta>)"
    by blast
  then
  show ?thesis
  proof (cases)
    case 1
    with \<open>p\<in>G\<close>
    show ?thesis by blast
  next
    case 2
    then
    obtain \<sigma> where "\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>)" "p forces\<^sub>a (\<sigma> \<in> \<tau>)" "p forces\<^sub>a (\<sigma> \<notin> \<theta>)"
      by blast
    moreover from this and \<open>p\<in>G\<close> and assms
    have "val(G,\<sigma>)\<in>val(G,\<tau>)"
      using IV240a[of \<sigma> \<tau>] transitivity[OF _ domain_closed[simplified]] by force
    moreover note \<open>val(G,\<tau>) = _\<close>
    ultimately
    obtain q where "q\<in>G" "q forces\<^sub>a (\<sigma> \<in> \<theta>)" 
      using IH[OF \<open>\<sigma>\<in>_\<close>]
      by auto
    moreover from this and \<open>p\<in>G\<close>
    obtain r where "r\<in>\<bbbP>" "r\<preceq>p" "r\<preceq>q"
      by blast
    ultimately
    have "r forces\<^sub>a (\<sigma> \<in> \<theta>)"
      using strengthening_mem by blast
    with \<open>r\<preceq>p\<close> \<open>p forces\<^sub>a (\<sigma> \<notin> \<theta>)\<close> \<open>r\<in>\<bbbP>\<close>
    have "False"
      unfolding forces_nmem_def by blast
    then
    show ?thesis by simp
  next (* copy-paste from case 2 mutatis mutandis*)
    case 3
    then
    obtain \<sigma> where "\<sigma>\<in>domain(\<tau>) \<union> domain(\<theta>)" "p forces\<^sub>a (\<sigma> \<in> \<theta>)" "p forces\<^sub>a (\<sigma> \<notin> \<tau>)"
      by blast
    moreover from this and \<open>p\<in>G\<close> and assms
    have "val(G,\<sigma>)\<in>val(G,\<theta>)"
      using IV240a[of \<sigma> \<theta>] transitivity[OF _ domain_closed[simplified]] by force
    moreover note \<open>val(G,\<tau>) = _\<close>
    ultimately
    obtain q where "q\<in>G" "q forces\<^sub>a (\<sigma> \<in> \<tau>)" 
      using IH[OF \<open>\<sigma>\<in>_\<close>]
      by auto
    moreover from this and \<open>p\<in>G\<close>
    obtain r where "r\<in>\<bbbP>" "r\<preceq>p" "r\<preceq>q"
      by blast
    ultimately
    have "r forces\<^sub>a (\<sigma> \<in> \<tau>)"
      using strengthening_mem by blast
    with \<open>r\<preceq>p\<close> \<open>p forces\<^sub>a (\<sigma> \<notin> \<tau>)\<close> \<open>r\<in>\<bbbP>\<close>
    have "False"
      unfolding forces_nmem_def by blast
    then
    show ?thesis by simp
  qed
qed

(* Lemma IV.2.40(b), full *)
lemma IV240b:
    "(\<tau>\<in>M\<longrightarrow>\<theta>\<in>M\<longrightarrow>val(G,\<tau>) = val(G,\<theta>) \<longrightarrow> (\<exists>p\<in>G. p forces\<^sub>a (\<tau> = \<theta>))) \<and>
     (\<tau>\<in>M\<longrightarrow>\<theta>\<in>M\<longrightarrow>val(G,\<tau>) \<in> val(G,\<theta>) \<longrightarrow> (\<exists>p\<in>G. p forces\<^sub>a (\<tau> \<in> \<theta>)))"
    (is "?Q(\<tau>,\<theta>) \<and> ?R(\<tau>,\<theta>)")
proof (intro forces_induction)
  fix \<tau> \<theta> p
  assume "\<sigma>\<in>domain(\<theta>) \<Longrightarrow> ?Q(\<tau>, \<sigma>)" for \<sigma>
  then  show "?R(\<tau>, \<theta>)"
    using IV240b_mem domain_closed transitivity by simp
next
  fix \<tau> \<theta> p
  assume "\<sigma> \<in> domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow> ?R(\<sigma>,\<tau>) \<and> ?R(\<sigma>,\<theta>)" for \<sigma>
  moreover from this
  have IH':"\<tau>\<in>M \<Longrightarrow> \<theta>\<in>M \<Longrightarrow> \<sigma> \<in> domain(\<tau>) \<union> domain(\<theta>) \<Longrightarrow>
          (val(G, \<sigma>) \<in> val(G, \<tau>) \<longrightarrow> (\<exists>q\<in>G. q forces\<^sub>a (\<sigma> \<in> \<tau>))) \<and>
          (val(G, \<sigma>) \<in> val(G, \<theta>) \<longrightarrow> (\<exists>q\<in>G. q forces\<^sub>a (\<sigma> \<in> \<theta>)))" for \<sigma>
    using domain_trans[OF trans_M]
    by blast
  ultimately
  show "?Q(\<tau>,\<theta>)"
    using IV240b_eq by auto
qed

lemma truth_lemma_mem:
  assumes
    "env\<in>list(M)"
    "n\<in>nat" "m\<in>nat" "n<length(env)" "m<length(env)"
  shows
    "(\<exists>p\<in>G. p \<tturnstile> Member(n,m) env)  \<longleftrightarrow>  M[G], map(val(G),env) \<Turnstile> Member(n,m)"
  using assms IV240a[of "nth(n,env)" "nth(m,env)"]
    IV240b[of "nth(n,env)" "nth(m,env)"]
    M_genericD
    Forces_Member[of _  "nth(n,env)" "nth(m,env)" env n m] map_val_in_MG
  by auto

lemma truth_lemma_eq:
  assumes
    "env\<in>list(M)"
    "n\<in>nat" "m\<in>nat" "n<length(env)" "m<length(env)"
  shows
    "(\<exists>p\<in>G. p \<tturnstile> Equal(n,m) env)  \<longleftrightarrow>  M[G], map(val(G),env) \<Turnstile> Equal(n,m)"
  using assms IV240a(1)[of "nth(n,env)" "nth(m,env)"]
    IV240b(1)[of "nth(n,env)" "nth(m,env)"]
    M_genericD
    Forces_Equal[of _  "nth(n,env)" "nth(m,env)" env n m] map_val_in_MG
  by auto

end \<comment> \<open>\<^locale>\<open>G_generic1\<close>\<close>

lemma arities_at_aux:
  assumes
    "n \<in> nat" "m \<in> nat" "env \<in> list(M)" "succ(n) \<union> succ(m) \<le> length(env)"
  shows
    "n < length(env)" "m < length(env)"
  using assms succ_leE[OF Un_leD1, of n "succ(m)" "length(env)"]
    succ_leE[OF Un_leD2, of "succ(n)" m "length(env)"] by auto

subsection\<open>The Strenghtening Lemma\<close>

context forcing_data1
begin

lemma strengthening_lemma:
  assumes
    "p\<in>\<bbbP>" "\<phi>\<in>formula" "r\<in>\<bbbP>" "r\<preceq>p"
    "env\<in>list(M)" "arity(\<phi>)\<le>length(env)"
  shows
    "p \<tturnstile> \<phi> env \<Longrightarrow> r \<tturnstile> \<phi> env"
  using assms(2-)
proof (induct arbitrary:env)
  case (Member n m)
  then
  have "n<length(env)" "m<length(env)"
    using arities_at_aux by simp_all
  moreover
  assume "env\<in>list(M)"
  moreover
  note assms Member
  ultimately
  show ?case
    using Forces_Member[of _ "nth(n,env)" "nth(m,env)" env n m]
      strengthening_mem[of p r "nth(n,env)" "nth(m,env)"] by simp
next
  case (Equal n m)
  then
  have "n<length(env)" "m<length(env)"
    using arities_at_aux by simp_all
  moreover
  assume "env\<in>list(M)"
  moreover
  note assms Equal
  ultimately
  show ?case
    using Forces_Equal[of _ "nth(n,env)" "nth(m,env)" env n m]
      strengthening_eq[of p r "nth(n,env)" "nth(m,env)"] by simp
next
  case (Nand \<phi> \<psi>)
  with assms
  show ?case
    using Forces_Nand transitivity[OF _ P_in_M] pair_in_M_iff
      transitivity[OF _ leq_in_M] leq_transD by auto
next
  case (Forall \<phi>)
  with assms
  have "p \<tturnstile> \<phi> ([x] @ env)" if "x\<in>M" for x
    using that Forces_Forall by simp
  with Forall
  have "r \<tturnstile> \<phi> ([x] @ env)" if "x\<in>M" for x
    using that pred_le2 by (simp)
  with assms Forall
  show ?case
    using Forces_Forall by simp
qed

subsection\<open>The Density Lemma\<close>

lemma arity_Nand_le:
  assumes "\<phi> \<in> formula" "\<psi> \<in> formula" "arity(Nand(\<phi>, \<psi>)) \<le> length(env)" "env\<in>list(A)"
  shows "arity(\<phi>) \<le> length(env)" "arity(\<psi>) \<le> length(env)"
  using assms
  by (rule_tac Un_leD1, rule_tac [5] Un_leD2, auto)

lemma dense_below_imp_forces:
  assumes
    "p\<in>\<bbbP>" "\<phi>\<in>formula"
    "env\<in>list(M)" "arity(\<phi>)\<le>length(env)"
  shows
    "dense_below({q\<in>\<bbbP>. (q \<tturnstile> \<phi> env)},p) \<Longrightarrow> (p \<tturnstile> \<phi> env)"
  using assms(2-)
proof (induct arbitrary:env)
  case (Member n m)
  then
  have "n<length(env)" "m<length(env)"
    using arities_at_aux by simp_all
  moreover
  assume "env\<in>list(M)"
  moreover
  note assms Member
  ultimately
  show ?case
    using Forces_Member[of _ "nth(n,env)" "nth(m,env)" env n m]
      density_mem[of p "nth(n,env)" "nth(m,env)"] by simp
next
  case (Equal n m)
  then
  have "n<length(env)" "m<length(env)"
    using arities_at_aux by simp_all
  moreover
  assume "env\<in>list(M)"
  moreover
  note assms Equal
  ultimately
  show ?case
    using Forces_Equal[of _ "nth(n,env)" "nth(m,env)" env n m]
      density_eq[of p "nth(n,env)" "nth(m,env)"] by simp
next
  case (Nand \<phi> \<psi>)
  {
    fix q
    assume "q\<in>M" "q\<in>\<bbbP>" "q\<preceq> p" "q \<tturnstile> \<phi> env"
    moreover
    note Nand
    moreover from calculation
    obtain d where "d\<in>\<bbbP>" "d \<tturnstile> Nand(\<phi>, \<psi>) env" "d\<preceq> q"
      using dense_belowI by auto
    moreover from calculation
    have "\<not>(d\<tturnstile> \<psi> env)" if "d \<tturnstile> \<phi> env"
      using that Forces_Nand refl_leq transitivity[OF _ P_in_M, of d] by auto
    moreover
    note arity_Nand_le[of \<phi> \<psi>]
    moreover from calculation
    have "d \<tturnstile> \<phi> env"
      using strengthening_lemma[of q \<phi> d env] Un_leD1 by auto
    ultimately
    have "\<not> (q \<tturnstile> \<psi> env)"
      using strengthening_lemma[of q \<psi> d env] by auto
  }
  with \<open>p\<in>\<bbbP>\<close>
  show ?case
    using Forces_Nand[symmetric, OF _ Nand(6,1,3)] by blast
next
  case (Forall \<phi>)
  have "dense_below({q\<in>\<bbbP>. q \<tturnstile> \<phi> ([a]@env)},p)" if "a\<in>M" for a
  proof
    fix r
    assume "r\<in>\<bbbP>" "r\<preceq>p"
    with \<open>dense_below(_,p)\<close>
    obtain q where "q\<in>\<bbbP>" "q\<preceq>r" "q \<tturnstile> Forall(\<phi>) env"
      by blast
    moreover
    note Forall \<open>a\<in>M\<close>
    moreover from calculation
    have "q \<tturnstile> \<phi> ([a]@env)"
      using Forces_Forall by simp
    ultimately
    show "\<exists>d \<in> {q\<in>\<bbbP>. q \<tturnstile> \<phi> ([a]@env)}. d \<in> \<bbbP> \<and> d\<preceq>r"
      by auto
  qed
  moreover
  note Forall(2)[of "Cons(_,env)"] Forall(1,3-5)
  ultimately
  have "p \<tturnstile> \<phi> ([a]@env)" if "a\<in>M" for a
    using that pred_le2 by simp
  with assms Forall
  show ?case using Forces_Forall by simp
qed

lemma density_lemma:
  assumes
    "p\<in>\<bbbP>" "\<phi>\<in>formula" "env\<in>list(M)" "arity(\<phi>)\<le>length(env)"
  shows
    "p \<tturnstile> \<phi> env   \<longleftrightarrow>   dense_below({q\<in>\<bbbP>. (q \<tturnstile> \<phi> env)},p)"
proof
  assume "dense_below({q\<in>\<bbbP>. (q \<tturnstile> \<phi> env)},p)"
  with assms
  show  "(p \<tturnstile> \<phi> env)"
    using dense_below_imp_forces by simp
next
  assume "p \<tturnstile> \<phi> env"
  with assms
  show "dense_below({q\<in>\<bbbP>. q \<tturnstile> \<phi> env},p)"
    using strengthening_lemma refl_leq by auto
qed

subsection\<open>The Truth Lemma\<close>

lemma Forces_And:
  assumes
    "p\<in>\<bbbP>" "env \<in> list(M)" "\<phi>\<in>formula" "\<psi>\<in>formula"
    "arity(\<phi>) \<le> length(env)" "arity(\<psi>) \<le> length(env)"
  shows
    "p \<tturnstile> And(\<phi>,\<psi>) env   \<longleftrightarrow>  (p \<tturnstile> \<phi> env) \<and> (p \<tturnstile> \<psi> env)"
proof
  assume "p \<tturnstile> And(\<phi>, \<psi>) env"
  with assms
  have "dense_below({r \<in> \<bbbP> . (r \<tturnstile> \<phi> env) \<and> (r \<tturnstile> \<psi> env)}, p)"
    using Forces_And_iff_dense_below by simp
  then
  have "dense_below({r \<in> \<bbbP> . (r \<tturnstile> \<phi> env)}, p)" "dense_below({r \<in> \<bbbP> . (r \<tturnstile> \<psi> env)}, p)"
    by blast+
  with assms
  show "(p \<tturnstile> \<phi> env) \<and> (p \<tturnstile> \<psi> env)"
    using density_lemma[symmetric] by simp
next
  assume "(p \<tturnstile> \<phi> env) \<and> (p \<tturnstile> \<psi> env)"
  have "dense_below({r \<in> \<bbbP> . (r \<tturnstile> \<phi> env) \<and> (r \<tturnstile> \<psi> env)}, p)"
  proof (intro dense_belowI bexI conjI, assumption)
    fix q
    assume "q\<in>\<bbbP>" "q\<preceq> p"
    with assms \<open>(p \<tturnstile> \<phi> env) \<and> (p \<tturnstile> \<psi> env)\<close>
    show "q\<in>{r \<in> \<bbbP> . (r \<tturnstile> \<phi> env) \<and> (r \<tturnstile> \<psi> env)}" "q\<preceq> q"
      using strengthening_lemma refl_leq by auto
  qed
  with assms
  show "p \<tturnstile> And(\<phi>,\<psi>) env"
    using Forces_And_iff_dense_below by simp
qed

lemma Forces_Nand_alt:
  assumes
    "p\<in>\<bbbP>" "env \<in> list(M)" "\<phi>\<in>formula" "\<psi>\<in>formula"
    "arity(\<phi>) \<le> length(env)" "arity(\<psi>) \<le> length(env)"
  shows
    "(p \<tturnstile> Nand(\<phi>,\<psi>) env) \<longleftrightarrow> (p \<tturnstile> Neg(And(\<phi>,\<psi>)) env)"
  using assms Forces_Nand Forces_And Forces_Neg by auto

end

context G_generic1
begin

lemma  truth_lemma_Neg:
  assumes
    "\<phi>\<in>formula" "env\<in>list(M)" "arity(\<phi>)\<le>length(env)" and
    IH: "(\<exists>p\<in>G. p \<tturnstile> \<phi> env) \<longleftrightarrow> M[G], map(val(G),env) \<Turnstile> \<phi>"
  shows
    "(\<exists>p\<in>G. p \<tturnstile> Neg(\<phi>) env)  \<longleftrightarrow>  M[G], map(val(G),env) \<Turnstile> Neg(\<phi>)"
proof (intro iffI, elim bexE, rule ccontr)
  (* Direct implication by contradiction *)
  fix p
  assume "p\<in>G" "p \<tturnstile> Neg(\<phi>) env" "\<not>(M[G],map(val(G),env) \<Turnstile> Neg(\<phi>))"
  moreover
  note assms
  moreover from calculation
  have "M[G], map(val(G),env) \<Turnstile> \<phi>" "p\<in>\<bbbP>"
    using map_val_in_MG by auto
  with IH
  obtain r where "r \<tturnstile> \<phi> env" "r\<in>G" "r\<in>\<bbbP>" by blast
  moreover from this and \<open>p\<in>G\<close>
  obtain q where "q\<preceq>p" "q\<preceq>r" "q\<in>G" "q\<in>\<bbbP>" "q\<in>M"
    using transitivity[OF _ P_in_M]
    by blast
  moreover from calculation
  have "q \<tturnstile> \<phi> env"
    using strengthening_lemma
    by simp
  with assms \<open>p \<tturnstile> _ _\<close> \<open>q\<preceq>p\<close> \<open>q\<in>M\<close> \<open>p\<in>\<bbbP>\<close> \<open>q\<in>\<bbbP>\<close>
   show "False"
    using Forces_Neg
    by auto
next
  assume "M[G], map(val(G),env) \<Turnstile> Neg(\<phi>)"
  with assms
  have "\<not> (M[G], map(val(G),env) \<Turnstile> \<phi>)"
    using map_val_in_MG by simp
  let ?D="{p\<in>\<bbbP>. (p \<tturnstile> \<phi> env) \<or> (p \<tturnstile> Neg(\<phi>) env)}"
  from assms
  have "?D \<in> M"
    using separation_disj separation_closed separation_forces by simp
  moreover
  have "?D \<subseteq> \<bbbP>" by auto
  moreover
  have "dense(?D)"
  proof
    fix q
    assume "q\<in>\<bbbP>"
    with assms
    show "\<exists>d\<in>{p \<in> \<bbbP> . (p \<tturnstile> \<phi> env) \<or> (p \<tturnstile> Neg(\<phi>) env)}. d\<preceq> q"
      using refl_leq Forces_Neg by (cases "q \<tturnstile> Neg(\<phi>) env", auto)
  qed
  ultimately
  obtain p where "p\<in>G" "(p \<tturnstile> \<phi> env) \<or> (p \<tturnstile> Neg(\<phi>) env)"
    by blast
  then
  consider (1) "p \<tturnstile> \<phi> env" | (2) "p \<tturnstile> Neg(\<phi>) env" by blast
  then
  show "\<exists>p\<in>G. (p \<tturnstile> Neg(\<phi>) env)"
  proof (cases)
    case 1
    with \<open>\<not> (M[G],map(val(G),env) \<Turnstile> \<phi>)\<close> \<open>p\<in>G\<close> IH
    show ?thesis
      by blast
  next
    case 2
    with \<open>p\<in>G\<close>
    show ?thesis by blast
  qed
qed

lemma truth_lemma_And:
  assumes
    "env\<in>list(M)" "\<phi>\<in>formula" "\<psi>\<in>formula"
    "arity(\<phi>)\<le>length(env)" "arity(\<psi>) \<le> length(env)"
    and
    IH: "(\<exists>p\<in>G. p \<tturnstile> \<phi> env)  \<longleftrightarrow>   M[G], map(val(G),env) \<Turnstile> \<phi>"
    "(\<exists>p\<in>G. p \<tturnstile> \<psi> env)  \<longleftrightarrow>   M[G], map(val(G),env) \<Turnstile> \<psi>"
  shows
    "(\<exists>p\<in>G. (p \<tturnstile> And(\<phi>,\<psi>) env)) \<longleftrightarrow> M[G] , map(val(G),env) \<Turnstile> And(\<phi>,\<psi>)"
  using assms map_val_in_MG Forces_And[OF M_genericD assms(1-5)]
proof (intro iffI, elim bexE)
  fix p
  assume "p\<in>G" "p \<tturnstile> And(\<phi>,\<psi>) env"
  with assms
  show "M[G], map(val(G),env) \<Turnstile> And(\<phi>,\<psi>)"
    using Forces_And[of  _ _ \<phi> \<psi>] map_val_in_MG M_genericD by auto
next
  assume "M[G], map(val(G),env) \<Turnstile> And(\<phi>,\<psi>)"
  moreover
  note assms
  moreover from calculation
  obtain q r where "q \<tturnstile> \<phi> env" "r \<tturnstile> \<psi> env" "q\<in>G" "r\<in>G" "r\<in>\<bbbP>" "q\<in>\<bbbP>"
    using map_val_in_MG Forces_And[OF M_genericD assms(1-5)] M_genericD by auto
  moreover from calculation
  obtain p where "p\<preceq>q" "p\<preceq>r" "p\<in>G"
    by auto
  moreover from calculation
  have "(p \<tturnstile> \<phi> env) \<and> (p \<tturnstile> \<psi> env)" (* can't solve as separate goals *)
    using strengthening_lemma[OF M_genericD] by force
  ultimately
  show "\<exists>p\<in>G. (p \<tturnstile> And(\<phi>,\<psi>) env)"
    using Forces_And[OF M_genericD assms(1-5)] by auto
qed

end

definition
  ren_truth_lemma :: "i\<Rightarrow>i" where
  "ren_truth_lemma(\<phi>) \<equiv>
    Exists(Exists(Exists(Exists(Exists(
    And(Equal(0,5),And(Equal(1,8),And(Equal(2,9),And(Equal(3,10),And(Equal(4,6),
    iterates(\<lambda>p. incr_bv(p)`5 , 6, \<phi>)))))))))))"

lemma ren_truth_lemma_type[TC] :
  "\<phi>\<in>formula \<Longrightarrow> ren_truth_lemma(\<phi>) \<in>formula"
  unfolding ren_truth_lemma_def
  by simp

lemma arity_ren_truth :
  assumes "\<phi>\<in>formula"
  shows "arity(ren_truth_lemma(\<phi>)) \<le> 6 \<union> succ(arity(\<phi>))"
proof -
  consider (lt) "5 <arity(\<phi>)" | (ge) "\<not> 5 < arity(\<phi>)"
    by auto
  then
  show ?thesis
  proof cases
    case lt
    consider (a) "5<arity(\<phi>)+\<^sub>\<omega>5"  | (b) "arity(\<phi>)+\<^sub>\<omega>5 \<le> 5"
      using not_lt_iff_le \<open>\<phi>\<in>_\<close> by force
    then
    show ?thesis
    proof cases
      case a
      with \<open>\<phi>\<in>_\<close> lt
      have "5 < succ(arity(\<phi>))" "5<arity(\<phi>)+\<^sub>\<omega>2"  "5<arity(\<phi>)+\<^sub>\<omega>3"  "5<arity(\<phi>)+\<^sub>\<omega>4"
        using succ_ltI by auto
      with \<open>\<phi>\<in>_\<close>
      have c:"arity(iterates(\<lambda>p. incr_bv(p)`5,5,\<phi>)) = 5+\<^sub>\<omega>arity(\<phi>)" (is "arity(?\<phi>') = _")
        using arity_incr_bv_lemma lt a
        by simp
      with \<open>\<phi>\<in>_\<close>
      have "arity(incr_bv(?\<phi>')`5) = 6+\<^sub>\<omega>arity(\<phi>)"
        using arity_incr_bv_lemma[of ?\<phi>' 5] a by auto
      with \<open>\<phi>\<in>_\<close>
      show ?thesis
        unfolding ren_truth_lemma_def
        using pred_Un_distrib union_abs1 Un_assoc[symmetric] a c union_abs2
        by (simp add:arity)
    next
      case b
      with \<open>\<phi>\<in>_\<close> lt
      have "5 < succ(arity(\<phi>))" "5<arity(\<phi>)+\<^sub>\<omega>2"  "5<arity(\<phi>)+\<^sub>\<omega>3"  "5<arity(\<phi>)+\<^sub>\<omega>4" "5<arity(\<phi>)+\<^sub>\<omega>5"
        using succ_ltI by auto
      with \<open>\<phi>\<in>_\<close>
      have "arity(iterates(\<lambda>p. incr_bv(p)`5,6,\<phi>)) = 6+\<^sub>\<omega>arity(\<phi>)" (is "arity(?\<phi>') = _")
        using arity_incr_bv_lemma lt
        by simp
      with \<open>\<phi>\<in>_\<close>
      show ?thesis
        unfolding ren_truth_lemma_def
        using pred_Un_distrib union_abs1 Un_assoc[symmetric]  union_abs2
        by (simp add:arity)
    qed
  next
    case ge
    with \<open>\<phi>\<in>_\<close>
    have "arity(\<phi>) \<le> 5" "pred^5(arity(\<phi>)) \<le> 5"
      using not_lt_iff_le le_trans[OF le_pred]
      by auto
    with \<open>\<phi>\<in>_\<close>
    have "arity(iterates(\<lambda>p. incr_bv(p)`5,6,\<phi>)) = arity(\<phi>)" "arity(\<phi>)\<le>6" "pred^5(arity(\<phi>)) \<le> 6"
      using arity_incr_bv_lemma ge le_trans[OF \<open>arity(\<phi>)\<le>5\<close>] le_trans[OF \<open>pred^5(arity(\<phi>))\<le>5\<close>]
      by auto
    with \<open>arity(\<phi>) \<le> 5\<close> \<open>\<phi>\<in>_\<close> \<open>pred^5(_) \<le> 5\<close>
    show ?thesis
      unfolding ren_truth_lemma_def
      using  pred_Un_distrib union_abs1 Un_assoc[symmetric] union_abs2
      by (simp add:arity)
  qed
qed

lemma sats_ren_truth_lemma:
  "[q,b,d,a1,a2,a3] @ env \<in> list(M) \<Longrightarrow> \<phi> \<in> formula \<Longrightarrow>
   (M, [q,b,d,a1,a2,a3] @ env \<Turnstile> ren_truth_lemma(\<phi>) ) \<longleftrightarrow>
   (M, [q,a1,a2,a3,b] @ env \<Turnstile> \<phi>)"
  unfolding ren_truth_lemma_def
  by (insert sats_incr_bv_iff [of _ _ M _ "[q,a1,a2,a3,b]"], simp)

context forcing_data1
begin

lemma truth_lemma' :
  assumes
    "\<phi>\<in>formula" "env\<in>list(M)" "arity(\<phi>) \<le> succ(length(env))"
  shows
    "separation(##M,\<lambda>d. \<exists>b\<in>M. \<forall>q\<in>\<bbbP>. q\<preceq>d \<longrightarrow> \<not>(q \<tturnstile> \<phi> ([b]@env)))"
proof -
  let ?rel_pred="\<lambda>M x a1 a2 a3. \<exists>b\<in>M. \<forall>q\<in>M. q\<in>a1 \<and> is_leq(##M,a2,q,x) \<longrightarrow>
                  \<not>(M, [q,a1,a2,a3,b] @ env \<Turnstile> forces(\<phi>))"
  let ?\<psi>="Exists(Forall(Implies(And(Member(0,3),is_leq_fm(4,0,2)),
          Neg(ren_truth_lemma(forces(\<phi>))))))"
  have "q\<in>M" if "q\<in>\<bbbP>" for q using that transitivity[OF _ P_in_M] by simp
  then
  have 1:"\<forall>q\<in>M. q\<in>\<bbbP> \<and> R(q) \<longrightarrow> Q(q) \<Longrightarrow> (\<forall>q\<in>\<bbbP>. R(q) \<longrightarrow> Q(q))" for R Q
    by auto
  then
  have "\<lbrakk>b \<in> M; \<forall>q\<in>M. q \<in> \<bbbP> \<and> q \<preceq> d \<longrightarrow> \<not>(q \<tturnstile> \<phi> ([b]@env))\<rbrakk> \<Longrightarrow>
         \<exists>c\<in>M. \<forall>q\<in>\<bbbP>. q \<preceq> d \<longrightarrow> \<not>(q \<tturnstile> \<phi> ([c]@env))" for b d
    by (rule bexI,simp_all)
  then
  have "?rel_pred(M,d,\<bbbP>,leq,\<one>) \<longleftrightarrow> (\<exists>b\<in>M. \<forall>q\<in>\<bbbP>. q\<preceq>d \<longrightarrow> \<not>(q \<tturnstile> \<phi> ([b]@env)))" if "d\<in>M" for d
    using that leq_abs assms
    by auto
  moreover
  have "?\<psi>\<in>formula" using assms by simp
  moreover
  have "(M, [d,\<bbbP>,leq,\<one>]@env \<Turnstile> ?\<psi>) \<longleftrightarrow> ?rel_pred(M,d,\<bbbP>,leq,\<one>)" if "d\<in>M" for d
    using assms that sats_is_leq_fm sats_ren_truth_lemma zero_in_M
    by simp
  moreover
  have "arity(?\<psi>) \<le> 4+\<^sub>\<omega>length(env)"
  proof -
    have eq:"arity(is_leq_fm(4, 0, 2)) = 5"
      using arity_is_leq_fm succ_Un_distrib ord_simp_union
      by simp
    with \<open>\<phi>\<in>_\<close>
    have "arity(?\<psi>) = 3 \<union> (pred^2(arity(ren_truth_lemma(forces(\<phi>)))))"
      using union_abs1 pred_Un_distrib by (simp add:arity)
    moreover
    have "... \<le> 3 \<union> (pred(pred(6 \<union> succ(arity(forces(\<phi>))))))" (is "_ \<le> ?r")
      using  \<open>\<phi>\<in>_\<close> Un_le_compat[OF le_refl[of 3]]
        le_imp_subset arity_ren_truth[of "forces(\<phi>)"]
        pred_mono
      by auto
    finally
    have "arity(?\<psi>) \<le> ?r" by simp
    have i:"?r \<le> 4 \<union> pred(arity(forces(\<phi>)))"
      using pred_Un_distrib pred_succ_eq \<open>\<phi>\<in>_\<close> Un_assoc[symmetric] union_abs1 by simp
    have h:"4 \<union> pred(arity(forces(\<phi>))) \<le> 4 \<union> (4+\<^sub>\<omega>length(env))"
      using  \<open>env\<in>_\<close> add_commute \<open>\<phi>\<in>_\<close>
        Un_le_compat[of 4 4,OF _ pred_mono[OF _ arity_forces_le[OF _ _ \<open>arity(\<phi>)\<le>_\<close>]] ]
        \<open>env\<in>_\<close> by auto
    with \<open>\<phi>\<in>_\<close> \<open>env\<in>_\<close>
    show ?thesis
      using le_trans[OF  \<open>arity(?\<psi>) \<le> ?r\<close>  le_trans[OF i h]] ord_simp_union by simp
  qed
  ultimately
  show ?thesis using assms
      separation_ax[of "?\<psi>" "[\<bbbP>,leq,\<one>]@env"]
      separation_cong[of "##M" "\<lambda>y. (M, [y,\<bbbP>,leq,\<one>]@env \<Turnstile>?\<psi>)"]
    by simp
qed

end

context G_generic1
begin

lemma truth_lemma:
  assumes
    "\<phi>\<in>formula"
    "env\<in>list(M)" "arity(\<phi>)\<le>length(env)"
  shows
    "(\<exists>p\<in>G. p \<tturnstile> \<phi> env)   \<longleftrightarrow>   M[G], map(val(G),env) \<Turnstile> \<phi>"
  using assms
proof (induct arbitrary:env)
  case (Member x y)
  then
  show ?case
    using truth_lemma_mem[OF \<open>env\<in>list(M)\<close> \<open>x\<in>nat\<close> \<open>y\<in>nat\<close>] arities_at_aux 
    by simp
next
  case (Equal x y)
  then
  show ?case
    using truth_lemma_eq[OF \<open>env\<in>list(M)\<close> \<open>x\<in>nat\<close> \<open>y\<in>nat\<close>] arities_at_aux by simp
next
  case (Nand \<phi> \<psi>)
  then
  show ?case
    using truth_lemma_And truth_lemma_Neg[of "\<cdot>\<phi> \<and> \<psi>\<cdot>"] Forces_Nand_alt
      M_genericD map_val_in_MG arity_Nand_le[of \<phi> \<psi>] FOL_arities by auto
next
  case (Forall \<phi>)
  then
  show ?case
  proof (intro iffI)
    assume "\<exists>p\<in>G. (p \<tturnstile> Forall(\<phi>) env)"
    then
    obtain p where "p\<in>G" "p\<in>M" "p\<in>\<bbbP>" "p \<tturnstile> Forall(\<phi>) env"
      using transitivity[OF _ P_in_M] by auto
    with \<open>env\<in>list(M)\<close> \<open>\<phi>\<in>formula\<close>
    have "p \<tturnstile> \<phi> ([x]@env)" if "x\<in>M" for x
      using that Forces_Forall by simp
    with \<open>p\<in>G\<close> \<open>\<phi>\<in>formula\<close> \<open>env\<in>_\<close> \<open>arity(Forall(\<phi>)) \<le> length(env)\<close>
      Forall(2)[of "Cons(_,env)"]
    show "M[G], map(val(G),env) \<Turnstile>  Forall(\<phi>)"
      using pred_le2 map_val_in_MG
      by (auto iff:GenExt_iff)
  next
    assume "M[G], map(val(G),env) \<Turnstile> Forall(\<phi>)"
    let ?D1="{d\<in>\<bbbP>. (d \<tturnstile> Forall(\<phi>) env)}"
    let ?D2="{d\<in>\<bbbP>. \<exists>b\<in>M. \<forall>q\<in>\<bbbP>. q\<preceq>d \<longrightarrow> \<not>(q \<tturnstile> \<phi> ([b]@env))}"
    define D where "D \<equiv> ?D1 \<union> ?D2"
    note \<open>arity(Forall(\<phi>)) \<le> length(env)\<close> \<open>\<phi>\<in>formula\<close> \<open>env\<in>list(M)\<close>
    moreover from this
    have ar\<phi>:"arity(\<phi>)\<le>succ(length(env))"
      using pred_le2 by simp
    moreover from calculation
    have "?D1\<in>M" using Collect_forces  by simp
    moreover from \<open>env\<in>list(M)\<close> \<open>\<phi>\<in>formula\<close>
    have "?D2\<in>M"
      using truth_lemma'[of \<phi>] separation_closed ar\<phi>
      by simp
    ultimately
    have "D\<in>M" unfolding D_def using Un_closed by simp
    moreover
    have "D \<subseteq> \<bbbP>" unfolding D_def by auto
    moreover
    have "dense(D)"
    proof
      fix p
      assume "p\<in>\<bbbP>"
      show "\<exists>d\<in>D. d\<preceq> p"
      proof (cases "p \<tturnstile> Forall(\<phi>) env")
        case True
        with \<open>p\<in>\<bbbP>\<close>
        show ?thesis unfolding D_def using refl_leq by blast
      next
        case False
        with Forall \<open>p\<in>\<bbbP>\<close>
        obtain b where "b\<in>M" "\<not>(p \<tturnstile> \<phi> ([b]@env))"
          using Forces_Forall by blast
        moreover from this \<open>p\<in>\<bbbP>\<close> Forall
        have "\<not>dense_below({q\<in>\<bbbP>. q \<tturnstile> \<phi> ([b]@env)},p)"
          using density_lemma pred_le2  by auto
        moreover from this
        obtain d where "d\<preceq>p" "\<forall>q\<in>\<bbbP>. q\<preceq>d \<longrightarrow> \<not>(q \<tturnstile> \<phi> ([b] @ env))"
          "d\<in>\<bbbP>" by blast
        ultimately
        show ?thesis unfolding D_def by auto
      qed
    qed
    moreover
    note generic
    ultimately
    obtain d where "d \<in> D" "d \<in> G" by blast
    then
    consider (1) "d\<in>?D1" | (2) "d\<in>?D2" unfolding D_def by blast
    then
    show "\<exists>p\<in>G. (p \<tturnstile> Forall(\<phi>) env)"
    proof (cases)
      case 1
      with \<open>d\<in>G\<close>
      show ?thesis by blast
    next
      case 2
      then
      obtain b where "b\<in>M" "\<forall>q\<in>\<bbbP>. q\<preceq>d \<longrightarrow>\<not>(q \<tturnstile> \<phi> ([b] @ env))"
        by blast
      moreover from this(1) and  \<open>M[G], _ \<Turnstile>  Forall(\<phi>)\<close> and
        Forall(2)[of "Cons(b,env)"] Forall(1,3-)
      obtain p where "p\<in>G" "p\<in>\<bbbP>" "p \<tturnstile> \<phi> ([b] @ env)"
        using pred_le2 map_val_in_MG M_genericD by (auto iff:GenExt_iff)
      moreover
      note \<open>d\<in>G\<close>
      ultimately
      obtain q where "q\<in>G" "q\<in>\<bbbP>" "q\<preceq>d" "q\<preceq>p"
        using M_genericD by force
      moreover from this and  \<open>p \<tturnstile> \<phi> ([b] @ env)\<close>
        Forall  \<open>b\<in>M\<close> \<open>p\<in>\<bbbP>\<close>
      have "q \<tturnstile> \<phi> ([b] @ env)"
        using pred_le2 strengthening_lemma by simp
      moreover
      note \<open>\<forall>q\<in>\<bbbP>. q\<preceq>d \<longrightarrow>\<not>(q \<tturnstile> \<phi> ([b] @ env))\<close>
      ultimately
      show ?thesis by simp
    qed
  qed
qed

end

context forcing_data1
begin

subsection\<open>The ``Definition of forcing''\<close>
lemma definition_of_forcing:
  assumes
    "p\<in>\<bbbP>" "\<phi>\<in>formula" "env\<in>list(M)" "arity(\<phi>)\<le>length(env)"
  shows
    "(p \<tturnstile> \<phi> env) \<longleftrightarrow>
     (\<forall>G. M_generic(G) \<and> p\<in>G \<longrightarrow> M[G], map(val(G),env) \<Turnstile> \<phi>)"
proof (intro iffI allI impI, elim conjE)
  fix G
  assume "(p \<tturnstile> \<phi> env)" "M_generic(G)" "p \<in> G"
  moreover from this
  interpret G_generic1 \<bbbP> leq \<one> M enum G 
    by (unfold_locales,simp)
  from calculation assms
  show "M[G], map(val(G),env) \<Turnstile> \<phi>"
    using truth_lemma[of \<phi>] by auto
next
  assume 1: "\<forall>G.(M_generic(G)\<and> p\<in>G) \<longrightarrow> M[G] , map(val(G),env) \<Turnstile> \<phi>"
  {
    fix r
    assume 2: "r\<in>\<bbbP>" "r\<preceq>p"
    then
    obtain G where "r\<in>G" "M_generic(G)"
      text\<open>Here we're using countability (via the existence of
        generic filters) of \<^term>\<open>M\<close> as a shortcut.\<close>
      using generic_filter_existence by auto
    moreover from this
    interpret G_generic1 \<bbbP> leq \<one> M enum G 
      by (unfold_locales,simp)
    from calculation 2 \<open>p\<in>\<bbbP>\<close>
    have "p\<in>G"
      using filter_leqD by auto
    moreover note 1
    ultimately
    have "M[G], map(val(G),env) \<Turnstile> \<phi>"
      by simp
    moreover
    note assms
    moreover from calculation
    obtain s where "s\<in>G" "(s \<tturnstile> \<phi> env)"
      using truth_lemma[of \<phi>] by blast
    moreover from this \<open>r\<in>G\<close>
    obtain q where "q\<in>G" "q\<preceq>s" "q\<preceq>r" "s\<in>\<bbbP>" "q\<in>\<bbbP>"
      by blast
    ultimately
    have "\<exists>q\<in>\<bbbP>. q\<preceq>r \<and> (q \<tturnstile> \<phi> env)"
      using strengthening_lemma[of s] by auto
  }
  then
  have "dense_below({q\<in>\<bbbP>. (q \<tturnstile> \<phi> env)},p)"
    unfolding dense_below_def by blast
  with assms
  show "(p \<tturnstile> \<phi> env)"
    using density_lemma by blast
qed

lemmas definability = forces_type

end \<comment> \<open>\<^locale>\<open>forcing_data1\<close>\<close>

end