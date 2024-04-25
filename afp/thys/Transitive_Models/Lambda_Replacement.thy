section\<open>Replacements using Lambdas\<close>

theory Lambda_Replacement
  imports
    Discipline_Function
begin

text\<open>In this theory we prove several instances of separation and replacement
in @{locale M_basic}. Moreover we introduce a new locale assuming two instances
of separation and six instances of lambda replacements (ie, replacement of
the form $\lambda x y.\ y=\langle x, f(x) \rangle$) and we prove a bunch of other
instances.\<close>


definition
  lam_replacement :: "[i\<Rightarrow>o,i\<Rightarrow>i] \<Rightarrow> o" where
  "lam_replacement(M,b) \<equiv> strong_replacement(M, \<lambda>x y. y = \<langle>x, b(x)\<rangle>)"

lemma separation_univ :
  shows "separation(M,M)"
  unfolding separation_def by auto

context M_trivial
begin

lemma lam_replacement_iff_lam_closed:
  assumes "\<forall>x[M]. M(b(x))"
  shows "lam_replacement(M, b) \<longleftrightarrow>  (\<forall>A[M]. M(\<lambda>x\<in>A. b(x)))"
  using assms lam_closed lam_funtype[of _ b, THEN Pi_memberD]
  unfolding lam_replacement_def strong_replacement_def
  by (auto intro:lamI dest:transM)
    (rule lam_closed, auto simp add:strong_replacement_def dest:transM)

lemma lam_replacement_imp_lam_closed:
  assumes "lam_replacement(M, b)" "M(A)" "\<forall>x\<in>A. M(b(x))"
  shows "M(\<lambda>x\<in>A. b(x))"
  using assms unfolding lam_replacement_def
  by (rule_tac lam_closed, auto simp add:strong_replacement_def dest:transM)

lemma lam_replacement_cong:
  assumes "lam_replacement(M,f)" "\<forall>x[M]. f(x) = g(x)" "\<forall>x[M]. M(f(x))"
  shows "lam_replacement(M,g)"
proof -
  note assms
  moreover from this
  have "\<forall>A[M]. M(\<lambda>x\<in>A. f(x))"
    using lam_replacement_iff_lam_closed
    by simp
  moreover from calculation
  have "(\<lambda>x\<in>A . f(x)) = (\<lambda>x\<in>A . g(x))" if "M(A)" for A
    using lam_cong[OF refl,of A f g] transM[OF _ that]
    by simp
  ultimately
  show ?thesis
    using lam_replacement_iff_lam_closed
    by simp
qed

end \<comment> \<open>\<^locale>\<open>M_trivial\<close>\<close>

context M_basic
begin

lemma separation_iff':
  assumes "separation(M,\<lambda>x . P(x))" "separation(M,\<lambda>x . Q(x))"
  shows "separation(M,\<lambda>x . P(x) \<longleftrightarrow> Q(x))"
  using assms separation_conj separation_imp iff_def
  by auto

lemma separation_in_constant :
  assumes "M(a)"
  shows "separation(M,\<lambda>x . x\<in>a)"
proof -
  have "{x\<in>A . x\<in>a} = A \<inter> a" for A by auto
  with \<open>M(a)\<close>
  show ?thesis using separation_iff Collect_abs
    by simp
qed

lemma separation_equal :
  shows "separation(M,\<lambda>x . x=a)"
proof -
  have "{x\<in>A . x=a} = (if a\<in>A then {a} else 0)" for A
    by auto
  then
  have "M({x\<in>A . x=a})" if "M(A)" for A
    using transM[OF _ \<open>M(A)\<close>] by simp
  then
  show ?thesis using separation_iff Collect_abs
    by simp
qed

lemma (in M_basic) separation_in_rev:
  assumes "(M)(a)"
  shows "separation(M,\<lambda>x . a\<in>x)"
proof -
  have eq: "{x\<in>A. a\<in>x} = Memrel(A\<union>{a}) `` {a}" for A
    unfolding ZF_Base.image_def
    by(intro equalityI,auto simp:mem_not_refl)
  moreover from assms
  have "M(Memrel(A\<union>{a}) `` {a})" if "M(A)" for A
    using that by simp
  ultimately
  show ?thesis
    using separation_iff Collect_abs
    by simp
qed

\<comment> \<open>\<close>
lemma lam_replacement_imp_strong_replacement_aux:
  assumes "lam_replacement(M, b)" "\<forall>x[M]. M(b(x))"
  shows "strong_replacement(M, \<lambda>x y. y = b(x))"
proof -
  {
    fix A
    note assms
    moreover
    assume "M(A)"
    moreover from calculation
    have "M(\<lambda>x\<in>A. b(x))" using lam_replacement_iff_lam_closed by auto
    ultimately
    have "M((\<lambda>x\<in>A. b(x))``A)" "\<forall>z[M]. z \<in> (\<lambda>x\<in>A. b(x))``A \<longleftrightarrow> (\<exists>x\<in>A. z = b(x))"
      by (auto simp:lam_def)
  }
  then
  show ?thesis unfolding strong_replacement_def
    by clarsimp (rule_tac x="(\<lambda>x\<in>A. b(x))``A" in rexI, auto)
qed

\<comment> \<open>This lemma could be modularized into the instantiation (fixing \<^term>\<open>X\<close>)
and the projection of the result of \<^term>\<open>f\<close>.\<close>
lemma strong_lam_replacement_imp_strong_replacement :
  assumes  "strong_replacement(M,\<lambda> x z . P(fst(x),snd(x)) \<and> z=\<langle>x,f(fst(x),snd(x))\<rangle>)"
    "\<And>A . M(A) \<Longrightarrow> \<forall>x\<in>A. P(X,x) \<longrightarrow> M(f(X,x))" "M(X)"
  shows "strong_replacement(M,\<lambda> x z . P(X,x) \<and> z=f(X,x))"
  unfolding strong_replacement_def
proof(clarsimp)
  fix A
  assume "M(A)"
  moreover from this \<open>M(X)\<close>
  have "M({X}\<times>A)" (is "M(?A)")
    by simp
  moreover
  have "fst(x) = X" if "x\<in>?A" for x
    using that by auto
  moreover from calculation assms
  have "M({z . x\<in>?A , P(fst(x),snd(x)) \<and> z=\<langle>x,f(fst(x),snd(x))\<rangle>})" (is "M(?F)")
    using transM[of _ ?A]
    by(rule_tac strong_replacement_closed,simp_all)
  moreover
  have "?F=({\<langle>x,f(fst(x),snd(x))\<rangle> . x\<in> {x\<in>?A .  P(fst(x),snd(x))}})" (is "_=(?G)")
    by auto
  moreover
  note \<open>M(?A)\<close>
  ultimately
  have "M(?G``?A)"
    by simp
  moreover
  have "?G``?A = {y . x\<in>?A , P(fst(x),snd(x)) \<and> y = f(fst(x),snd(x))}" (is "_=(?H)")
    by auto
  ultimately
  show "\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x\<in>A. P(X,x) \<and> b = f(X,x))"
    by(rule_tac rexI[of _ ?H],auto,force)
qed

lemma lam_replacement_imp_RepFun_Lam:
  assumes "lam_replacement(M, f)" "M(A)"
  shows "M({y . x\<in>A , M(y) \<and> y=\<langle>x,f(x)\<rangle>})"
proof -
  from assms
  obtain Y where 1:"M(Y)" "\<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x,f(x)\<rangle>)"
    unfolding lam_replacement_def strong_replacement_def
    by auto
  moreover from calculation
  have "Y = {y . x\<in>A , M(y) \<and> y = \<langle>x,f(x)\<rangle>}" (is "Y=?R")
  proof(intro equalityI subsetI)
    fix y
    assume "y\<in>Y"
    moreover from this 1
    obtain x where "x\<in>A" "y=\<langle>x,f(x)\<rangle>" "M(y)"
      using transM[OF _ \<open>M(Y)\<close>] by auto
    ultimately
    show "y\<in>?R"
      by auto
  next
    fix z
    assume "z\<in>?R"
    moreover from this
    obtain a where "a\<in>A" "z=\<langle>a,f(a)\<rangle>" "M(a)" "M(f(a))"
      using transM[OF _ \<open>M(A)\<close>]
      by auto
    ultimately
    show "z\<in>Y" using 1 by simp
  qed
  ultimately
  show ?thesis by auto
qed

lemma lam_closed_imp_closed:
  assumes "\<forall>A[M]. M(\<lambda>x\<in>A. f(x))"
  shows "\<forall>x[M]. M(f(x))"
proof
  fix x
  assume "M(x)"
  moreover from this and assms
  have "M(\<lambda>x\<in>{x}. f(x))" by simp
  ultimately
  show "M(f(x))"
    using image_lam[of "{x}" "{x}" f]
      image_closed[of "{x}" "(\<lambda>x\<in>{x}. f(x))"] by (auto dest:transM)
qed

lemma lam_replacement_if:
  assumes "lam_replacement(M,f)" "lam_replacement(M,g)" "separation(M,b)"
    "\<forall>x[M]. M(f(x))" "\<forall>x[M]. M(g(x))"
  shows "lam_replacement(M, \<lambda>x. if b(x) then f(x) else g(x))"
proof -
  let ?G="\<lambda>x. if b(x) then f(x) else g(x)"
  let ?b="\<lambda>A . {x\<in>A. b(x)}" and ?b'="\<lambda>A . {x\<in>A. \<not>b(x)}"
  have eq:"(\<lambda>x\<in>A . ?G(x)) = (\<lambda>x\<in>?b(A) . f(x)) \<union> (\<lambda>x\<in>?b'(A).g(x))" for A
    unfolding lam_def by auto
  have "?b'(A) = A - ?b(A)" for A by auto
  moreover
  have "M(?b(A))" if "M(A)" for A using assms that by simp
  moreover from calculation
  have "M(?b'(A))" if "M(A)" for A using that by simp
  moreover from calculation assms
  have "M(\<lambda>x\<in>?b(A). f(x))" "M(\<lambda>x\<in>?b'(A) . g(x))" if "M(A)" for A
    using lam_replacement_iff_lam_closed that
    by simp_all
  moreover from this
  have "M((\<lambda>x\<in>?b(A) . f(x)) \<union> (\<lambda>x\<in>?b'(A).g(x)))" if "M(A)" for A
    using that by simp
  ultimately
  have "M(\<lambda>x\<in>A. if b(x) then f(x) else g(x))" if "M(A)" for A
    using that eq by simp
  with assms
  show ?thesis using lam_replacement_iff_lam_closed by simp
qed

lemma lam_replacement_constant: "M(b) \<Longrightarrow> lam_replacement(M,\<lambda>_. b)"
  unfolding lam_replacement_def strong_replacement_def
  by safe (rule_tac x="_\<times>{b}" in rexI; blast)

subsection\<open>Replacement instances obtained through Powerset\<close>

txt\<open>The next few lemmas provide bounds for certain constructions.\<close>

lemma not_functional_Replace_0:
  assumes "\<not>(\<forall>y y'. P(y) \<and> P(y') \<longrightarrow> y=y')"
  shows "{y . x \<in> A, P(y)} = 0"
  using assms by (blast elim!: ReplaceE)

lemma Replace_in_Pow_rel:
  assumes "\<And>x b. x \<in> A \<Longrightarrow> P(x,b) \<Longrightarrow> b \<in> U" "\<forall>x\<in>A. \<forall>y y'. P(x,y) \<and> P(x,y') \<longrightarrow> y=y'"
    "separation(M, \<lambda>y. \<exists>x[M]. x \<in> A \<and> P(x, y))"
    "M(U)" "M(A)"
  shows "{y . x \<in> A, P(x, y)} \<in> Pow\<^bsup>M\<^esup>(U)"
proof -
  from assms
  have "{y . x \<in> A, P(x, y)} \<subseteq> U"
    "z \<in> {y . x \<in> A, P(x, y)} \<Longrightarrow> M(z)" for z
    by (auto dest:transM)
  with assms
  have "{y . x \<in> A, P(x, y)} = {y\<in>U . \<exists>x[M]. x\<in>A \<and> P(x,y)}"
    by (intro equalityI) (auto, blast)
  with assms
  have "M({y . x \<in> A, P(x, y)})"
    by simp
  with assms
  show ?thesis
    using mem_Pow_rel_abs by auto
qed

lemma Replace_sing_0_in_Pow_rel:
  assumes "\<And>b. P(b) \<Longrightarrow> b \<in> U"
    "separation(M, \<lambda>y. P(y))" "M(U)"
  shows "{y . x \<in> {0}, P(y)} \<in> Pow\<^bsup>M\<^esup>(U)"
proof (cases "\<forall>y y'. P(y) \<and> P(y') \<longrightarrow> y=y'")
  case True
  with assms
  show ?thesis by (rule_tac Replace_in_Pow_rel) auto
next
  case False
  with assms
  show ?thesis
    using nonempty not_functional_Replace_0[of P "{0}"] Pow_rel_char by auto
qed

lemma The_in_Pow_rel_Union:
  assumes "\<And>b. P(b) \<Longrightarrow> b \<in> U" "separation(M, \<lambda>y. P(y))" "M(U)"
  shows "(THE i. P(i)) \<in> Pow\<^bsup>M\<^esup>(\<Union>U)"
proof -
  note assms
  moreover from this
  have "(THE i. P(i)) \<in> Pow(\<Union>U)"
    unfolding the_def by auto
  moreover from assms
  have "M(THE i. P(i))"
    using Replace_sing_0_in_Pow_rel[of P U] unfolding the_def
    by (auto dest:transM)
  ultimately
  show ?thesis
    using Pow_rel_char by auto
qed

lemma separation_least: "separation(M, \<lambda>y. Ord(y) \<and> P(y) \<and> (\<forall>j. j < y \<longrightarrow> \<not> P(j)))"
  unfolding separation_def
proof
  fix z
  assume "M(z)"
  have "M({x \<in> z . x \<in> z \<and> Ord(x) \<and> P(x) \<and> (\<forall>j. j < x \<longrightarrow> \<not> P(j))})"
    (is "M(?y)")
  proof (cases "\<exists>x\<in>z. Ord(x) \<and> P(x) \<and> (\<forall>j. j < x \<longrightarrow> \<not> P(j))")
    case True
    with \<open>M(z)\<close>
    have "\<exists>x[M]. ?y = {x}"
      by (safe, rename_tac x, rule_tac x=x in rexI)
        (auto dest:transM, intro equalityI, auto elim:Ord_linear_lt)
    then
    show ?thesis
      by auto
  next
    case False
    then
    have "{x \<in> z . x \<in> z \<and> Ord(x) \<and> P(x) \<and> (\<forall>j. j < x \<longrightarrow> \<not> P(j))} = 0"
      by auto
    then
    show ?thesis by auto
  qed
  moreover from this
  have "\<forall>x[M]. x \<in> ?y \<longleftrightarrow> x \<in> z \<and> Ord(x) \<and> P(x) \<and> (\<forall>j. j < x \<longrightarrow> \<not> P(j))" by simp
  ultimately
  show "\<exists>y[M]. \<forall>x[M]. x \<in> y \<longleftrightarrow> x \<in> z \<and> Ord(x) \<and> P(x) \<and> (\<forall>j. j < x \<longrightarrow> \<not> P(j))"
    by blast
qed

lemma Least_in_Pow_rel_Union:
  assumes "\<And>b. P(b) \<Longrightarrow> b \<in> U"
    "M(U)"
  shows "(\<mu> i. P(i)) \<in> Pow\<^bsup>M\<^esup>(\<Union>U)"
  using assms separation_least unfolding Least_def
  by (rule_tac The_in_Pow_rel_Union) simp

lemma bounded_lam_replacement:
  fixes U
  assumes "\<forall>X[M]. \<forall>x\<in>X. f(x) \<in> U(X)"
    and separation_f:"\<forall>A[M]. separation(M,\<lambda>y. \<exists>x[M]. x\<in>A \<and> y = \<langle>x, f(x)\<rangle>)"
    and U_closed [intro,simp]: "\<And>X. M(X) \<Longrightarrow> M(U(X))"
  shows "lam_replacement(M, f)"
proof -
  have "M(\<lambda>x\<in>A. f(x))" if "M(A)" for A
  proof -
    have "(\<lambda>x\<in>A. f(x)) = {y\<in> Pow\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(A \<union> U(A))). \<exists>x[M]. x\<in>A \<and> y = \<langle>x, f(x)\<rangle>}"
      using \<open>M(A)\<close> unfolding lam_def
    proof (intro equalityI, auto)
      fix x
      assume "x\<in>A"
      moreover
      note \<open>M(A)\<close>
      moreover from calculation assms
      have "f(x) \<in> U(A)" by simp
      moreover from calculation
      have "{x, f(x)} \<in> Pow\<^bsup>M\<^esup>(A \<union> U(A))" "{x,x} \<in> Pow\<^bsup>M\<^esup>(A \<union> U(A))"
        using Pow_rel_char[of "A \<union> U(A)"] by (auto dest:transM)
      ultimately
      show "\<langle>x, f(x)\<rangle> \<in> Pow\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(A \<union> U(A)))"
        using Pow_rel_char[of "Pow\<^bsup>M\<^esup>(A \<union> U(A))"] unfolding Pair_def
        by (auto dest:transM)
    qed
    moreover from \<open>M(A)\<close>
    have "M({y\<in> Pow\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(A \<union> U(A))). \<exists>x[M]. x\<in>A \<and> y = \<langle>x, f(x)\<rangle>})"
      using separation_f
      by (rule_tac separation_closed) simp_all
    ultimately
    show ?thesis
      by simp
  qed
  moreover from this
  have "\<forall>x[M]. M(f(x))"
    using lam_closed_imp_closed by simp
  ultimately
  show ?thesis
    using assms
    by (rule_tac lam_replacement_iff_lam_closed[THEN iffD2]) simp_all
qed

lemma fst_in_double_Union:
  assumes "x\<in>X"
  shows "fst(x) \<in> {0} \<union> \<Union>\<Union>X"
proof -
  have "fst(x) \<in> {0} \<union> \<Union>x" for x
    unfolding fst_def
    using the_0 fst_conv
    by(cases "\<exists>!a.\<exists>b. x = \<langle>a,b\<rangle>", auto, simp add:Pair_def)
  with assms
  show ?thesis by auto
qed

lemma snd_in_double_Union:
  assumes "x\<in>X"
  shows "snd(x) \<in> {0} \<union> \<Union>\<Union>X"
proof -
  have "snd(x) \<in> {0} \<union> \<Union>x" for x
    unfolding snd_def
    using the_0 snd_conv
    by(cases "\<exists>!a.\<exists>b. x = \<langle>a,b\<rangle>", auto, simp add:Pair_def)
  with assms
  show ?thesis by auto
qed

lemma bounded_lam_replacement_binary:
  fixes U
  assumes "\<forall>X[M]. \<forall>x\<in>X. \<forall>y\<in>X. f(x,y) \<in> U(X)"
    and separation_f:"\<forall>A[M]. separation(M,\<lambda>y. \<exists>x[M]. x\<in>A \<and> y = \<langle>x, f(fst(x),snd(x))\<rangle>)"
    and U_closed [intro,simp]: "\<And>X. M(X) \<Longrightarrow> M(U(X))"
  shows "lam_replacement(M, \<lambda>r . f(fst(r),snd(r)))"
proof -
  have "M(\<lambda>x\<in>A. f(fst(x),snd(x)))" if "M(A)" for A
  proof -
    have "(\<lambda>x\<in>A. f(fst(x),snd(x))) =
      {y\<in> Pow\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(A \<union> U({0} \<union> \<Union>\<Union>A))). \<exists>x[M]. x\<in>A \<and> y = \<langle>x, f(fst(x),snd(x))\<rangle>}"
      using \<open>M(A)\<close> unfolding lam_def
    proof (intro equalityI, auto)
      fix x
      assume "x\<in>A"
      moreover
      note \<open>M(A)\<close>
      moreover from calculation assms
      have "f(fst(x),snd(x)) \<in> U({0} \<union> \<Union>\<Union>A)"
        using fst_in_double_Union snd_in_double_Union by simp
      moreover from calculation
      have "{x, f(fst(x),snd(x))} \<in> Pow\<^bsup>M\<^esup>(A \<union> U({0} \<union> \<Union>\<Union>A))"
        "{x,x} \<in> Pow\<^bsup>M\<^esup>(A \<union> U({0} \<union> \<Union>\<Union>A))"
        using Pow_rel_char[of "A \<union> U({0} \<union> \<Union>\<Union>A)"] by (auto dest:transM)
      ultimately
      show "\<langle>x, f(fst(x),snd(x))\<rangle> \<in> Pow\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(A \<union> U({0} \<union> \<Union>\<Union>A)))"
        using Pow_rel_char[of "Pow\<^bsup>M\<^esup>(A \<union> U({0} \<union> \<Union>\<Union>A))"] unfolding Pair_def
        by (auto dest:transM)
    qed
    moreover from \<open>M(A)\<close>
    have "M({y\<in> Pow\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(A \<union> U({0} \<union> \<Union>\<Union>A))). \<exists>x[M]. x\<in>A \<and> y = \<langle>x, f(fst(x),snd(x))\<rangle>})"
      using separation_f
      by (rule_tac separation_closed) simp_all
    ultimately
    show ?thesis
      by simp
  qed
  moreover from this
  have "\<forall>x[M]. M(f(fst(x),snd(x)))"
    using lam_closed_imp_closed[of "\<lambda>x. f(fst(x),snd(x))"] by simp
  ultimately
  show ?thesis
    using assms
    by (rule_tac lam_replacement_iff_lam_closed[THEN iffD2]) simp_all
qed

\<comment> \<open>Below we assume the replacement instance for @{term fst}. Alternatively it follows from the
instance of separation assumed in this lemma.\<close>
lemma lam_replacement_fst':
  assumes "\<forall>A[M]. separation(M, \<lambda>y. \<exists>x[M]. x\<in>A \<and> y = \<langle>x, fst(x)\<rangle>)"
  shows "lam_replacement(M,fst)"
  using fst_in_double_Union assms
    bounded_lam_replacement[of fst "\<lambda>X. {0} \<union> \<Union>\<Union>X"] by simp

lemma lam_replacement_snd':
  assumes "\<forall>A[M]. separation(M, \<lambda>y. \<exists>x[M]. x\<in>A \<and> y = \<langle>x, snd(x)\<rangle>)"
  shows "lam_replacement(M,snd)"
  using snd_in_double_Union assms
    bounded_lam_replacement[of snd "\<lambda>X. {0} \<union> \<Union>\<Union>X"] by simp

\<comment> \<open>We can prove this separation in the locale introduced below.\<close>
lemma lam_replacement_restrict:
  assumes "\<forall>A[M]. separation(M, \<lambda>y. \<exists>x[M]. x\<in>A \<and> y = \<langle>x, restrict(x,B)\<rangle>)"  "M(B)"
  shows "lam_replacement(M, \<lambda>r . restrict(r,B))"
proof -
  from assms
  have "restrict(r,B)\<in>Pow\<^bsup>M\<^esup>(\<Union>R)" if "M(R)" "r\<in>R" for r R
    using Union_upper subset_Pow_Union subset_trans[OF restrict_subset]
      Pow_rel_char that transM[of _ R]
    by auto
  with assms
  show ?thesis
    using bounded_lam_replacement[of "\<lambda>r . restrict(r,B)" "\<lambda>X. Pow\<^bsup>M\<^esup>(\<Union>X)"]
    by simp
qed

lemma lam_replacement_Union' :
  assumes  "\<forall>A[M]. separation(M, \<lambda>y. \<exists>x[M]. x \<in> A \<and> y = \<langle>x, \<Union>x\<rangle>)"
  shows "lam_replacement(M,Union)"
proof -
  have "\<Union>x \<in> Pow(\<Union>\<Union>A)" if "x\<in>A" for x A
    using that by auto
  then
  have "\<Union>x \<in> Pow\<^bsup>M\<^esup>(\<Union>\<Union>A)" if "M(A)" "x\<in>A" for x A
    using that transM[of x A] Pow_rel_char
    by auto
  with assms
  show ?thesis
    using bounded_lam_replacement[where U="\<lambda>A . Pow\<^bsup>M\<^esup>(\<Union>\<Union>A)"]
    by auto
qed

lemma Image_in_Pow_rel_Union3:
  assumes "x\<in>X" "y\<in>X" "M(X)"
  shows "Image(x,y) \<in> Pow\<^bsup>M\<^esup>(\<Union>\<Union>\<Union>X)"
proof -
  from assms
  have "\<langle>a, b\<rangle> \<in> x \<Longrightarrow> b \<in> \<Union>\<Union>x" for a b
    unfolding Pair_def by (auto dest:transM)
  moreover from this and assms
  have "\<langle>a, b\<rangle> \<in> x \<Longrightarrow> M(b)" for a b
    using transM[of _  X] transM[of _  x]
    by auto
  ultimately
  show ?thesis
    using assms transM[of _  X] transM[of _  x] mem_Pow_rel_abs
    by auto fast
qed

lemma lam_replacement_Image':
  assumes
    "\<forall>A[M]. separation(M,\<lambda>y. \<exists>x[M]. x\<in>A \<and> y = \<langle>x, Image(fst(x),snd(x))\<rangle>)"
  shows
    "lam_replacement(M, \<lambda>r . Image(fst(r),snd(r)))"
  using assms Image_in_Pow_rel_Union3
  by (rule_tac bounded_lam_replacement_binary[of _ "\<lambda>X. Pow\<^bsup>M\<^esup>(\<Union>\<Union>\<Union>X)"]) auto

lemma minimum_in_Union:
  assumes "x\<in>X" "y\<in>X"
  shows "minimum(x,y) \<in> {0} \<union> \<Union>X"
  using assms minimum_in'
  by auto

lemma lam_replacement_minimum':
  assumes
    "\<forall>A[M]. separation(M,\<lambda>y. \<exists>x[M]. x\<in>A \<and> y = \<langle>x, minimum(fst(x),snd(x))\<rangle>)"
  shows
    "lam_replacement(M, \<lambda>r . minimum(fst(r),snd(r)))"
  using assms minimum_in_Union
  by (rule_tac bounded_lam_replacement_binary[of _ "\<lambda>X. {0} \<union> \<Union>X"]) auto

lemma lam_replacement_Pow_rel:
  assumes "\<forall>A[M]. separation(M, \<lambda>y. \<exists>x[M]. x \<in> A \<and> y = \<langle>x, Pow_rel(M,x)\<rangle>)"
  shows "lam_replacement(M,Pow_rel(M))"
proof -
  have "Pow_rel(M,x) \<in> Pow(Pow(\<Union>A))" if "x\<in>A" "M(A)" for x A
    using that transM[of x A] def_Pow_rel[of _ x] by (auto dest:transM)
  then
  have "Pow_rel(M,x) \<in> Pow(Pow\<^bsup>M\<^esup>(\<Union>A))" if "M(A)" "x\<in>A" for x A
    using that transM[of x A] Pow_rel_char
    by auto
  then
  have "Pow_rel(M,x) \<in> Pow\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(\<Union>A))" if "M(A)" "x\<in>A" for x A
    using that transM[of x A] Pow_rel_char[of "Pow\<^bsup>M\<^esup>(\<Union>A)"]
    by auto
  with assms
  show ?thesis
    using bounded_lam_replacement[where U="\<lambda>A. Pow\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(\<Union>A))"]
    by auto
qed

end \<comment> \<open>\<^locale>\<open>M_basic\<close>\<close>

definition
  middle_del :: "i\<Rightarrow>i\<Rightarrow>i" where
  "middle_del(x,y) \<equiv> \<langle>fst(x),snd(y)\<rangle>"

relativize functional "middle_del" "middle_del_rel"
relationalize "middle_del_rel" "is_middle_del"
synthesize "is_middle_del" from_definition
arity_theorem for "is_middle_del_fm"

context M_basic
begin

lemma middle_del_in_cartprod:
  assumes "x\<in>X" "y\<in>X" "M(X)"
  shows "middle_del(x,y) \<in> ({0} \<union> \<Union>\<Union>X) \<times> ({0} \<union> \<Union>\<Union>X)"
  using assms Pow_rel_char transM[of _ X] fst_in_double_Union snd_in_double_Union
  unfolding middle_del_def by auto

lemma lam_replacement_middle_del':
  assumes
    "\<forall>A[M]. separation(M,\<lambda>y. \<exists>x[M]. x\<in>A \<and> y = \<langle>x, middle_del(fst(x),snd(x))\<rangle>)"
  shows
    "lam_replacement(M, \<lambda>r . middle_del(fst(r),snd(r)))"
  using assms middle_del_in_cartprod
  by (rule_tac bounded_lam_replacement_binary[of _ "\<lambda>X. ({0} \<union> \<Union>\<Union>X) \<times> ({0} \<union> \<Union>\<Union>X)"]) auto

end \<comment> \<open>\<^locale>\<open>M_basic\<close>\<close>

definition
  prodRepl :: "i\<Rightarrow>i\<Rightarrow>i" where
  "prodRepl(x,y) \<equiv> \<langle>snd(x),\<langle>fst(x),snd(y)\<rangle>\<rangle>"

relativize functional "prodRepl" "prodRepl_rel"
relationalize "prodRepl_rel" "is_prodRepl"
synthesize "is_prodRepl" from_definition
arity_theorem for "is_prodRepl_fm"

context M_basic
begin

lemma prodRepl_in_cartprod:
  assumes "x\<in>X" "y\<in>X" "M(X)"
  shows "prodRepl(x,y) \<in> ({0} \<union> \<Union>\<Union>X) \<times> ({0} \<union> \<Union>\<Union>X) \<times> ({0} \<union> \<Union>\<Union>X)"
  using assms Pow_rel_char transM[of _ X] fst_in_double_Union snd_in_double_Union
  unfolding prodRepl_def by auto

lemma lam_replacement_prodRepl':
  assumes
    "\<forall>A[M]. separation(M,\<lambda>y. \<exists>x[M]. x\<in>A \<and> y = \<langle>x, prodRepl(fst(x),snd(x))\<rangle>)"
  shows
    "lam_replacement(M, \<lambda>r . prodRepl(fst(r),snd(r)))"
  using assms prodRepl_in_cartprod
  by (rule_tac bounded_lam_replacement_binary[of _
        "\<lambda>X. ({0} \<union> \<Union>\<Union>X) \<times> ({0} \<union> \<Union>\<Union>X) \<times> ({0} \<union> \<Union>\<Union>X)"]) auto

end \<comment> \<open>\<^locale>\<open>M_basic\<close>\<close>

context M_Perm
begin

lemma inj_rel_in_Pow_rel_Pow_rel:
  assumes "x\<in>X" "y\<in>X" "M(X)"
  shows "inj\<^bsup>M\<^esup>(x,y) \<in> Pow\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(\<Union>X \<times> \<Union>X))"
  using assms transM[of _  X] mem_Pow_rel_abs inj_def Pi_def
  by clarsimp (use inj_rel_char in auto)

lemma lam_replacement_inj_rel':
  assumes
    "\<forall>A[M]. separation(M,\<lambda>y. \<exists>x[M]. x\<in>A \<and> y = \<langle>x, inj\<^bsup>M\<^esup>(fst(x),snd(x))\<rangle>)"
  shows
    "lam_replacement(M, \<lambda>r . inj\<^bsup>M\<^esup>(fst(r),snd(r)))"
  using assms inj_rel_in_Pow_rel_Pow_rel
  by (rule_tac bounded_lam_replacement_binary[of _ "\<lambda>X. Pow\<^bsup>M\<^esup>(Pow\<^bsup>M\<^esup>(\<Union>X \<times> \<Union>X))"]) auto

end \<comment> \<open>\<^locale>\<open>M_Perm\<close>\<close>

locale M_replacement = M_basic +
  assumes
    lam_replacement_fst: "lam_replacement(M,fst)"
    and
    lam_replacement_snd: "lam_replacement(M,snd)"
    and
    lam_replacement_Union: "lam_replacement(M,Union)"
    and
    lam_replacement_middle_del: "lam_replacement(M, \<lambda>r. middle_del(fst(r),snd(r)))"
    and
    lam_replacement_prodRepl: "lam_replacement(M, \<lambda>r. prodRepl(fst(r),snd(r)))"
    and
    lam_replacement_Image:"lam_replacement(M, \<lambda>p. fst(p) `` snd(p))"
    and
    middle_separation: "separation(M, \<lambda>x. snd(fst(x))=fst(snd(x)))"
    and
    separation_fst_in_snd: "separation(M, \<lambda>y. fst(snd(y)) \<in> snd(snd(y)))"
begin

\<comment> \<open>This lemma is similar to @{thm [source] strong_lam_replacement_imp_strong_replacement}
and @{thm [source] lam_replacement_imp_strong_replacement_aux} but does not require
\<^term>\<open>g\<close> to be closed under \<^term>\<open>M\<close>.\<close>
lemma lam_replacement_imp_strong_replacement:
  assumes "lam_replacement(M, f)"
  shows "strong_replacement(M, \<lambda>x y. y = f(x))"
proof -
  {
    fix A
    assume "M(A)"
    moreover from calculation assms
    obtain Y where 1:"M(Y)" "\<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x,f(x)\<rangle>)"
      unfolding lam_replacement_def strong_replacement_def
      by auto
    moreover from this
    have "M({snd(b) . b \<in> Y})"
      using transM[OF _ \<open>M(Y)\<close>] lam_replacement_snd lam_replacement_imp_strong_replacement_aux
        RepFun_closed by simp
    moreover
    have "{snd(b) . b \<in> Y} = {y . x\<in>A , M(f(x)) \<and> y=f(x)}" (is "?L=?R")
    proof(intro equalityI subsetI)
      fix x
      assume "x\<in>?L"
      moreover from this
      obtain b where "b\<in>Y" "x=snd(b)" "M(b)"
        using transM[OF _ \<open>M(Y)\<close>] by auto
      moreover from this 1
      obtain a where "a\<in>A" "b=\<langle>a,f(a)\<rangle>" by auto
      moreover from calculation
      have "x=f(a)" by simp
      ultimately show "x\<in>?R"
        by auto
    next
      fix z
      assume "z\<in>?R"
      moreover from this
      obtain a where "a\<in>A" "z=f(a)" "M(a)" "M(f(a))"
        using transM[OF _ \<open>M(A)\<close>]
        by auto
      moreover from calculation this 1
      have "z=snd(\<langle>a,f(a)\<rangle>)" "\<langle>a,f(a)\<rangle> \<in> Y" by auto
      ultimately
      show "z\<in>?L" by force
    qed
    ultimately
    have "\<exists>Z[M]. \<forall>z[M]. z\<in>Z \<longleftrightarrow> (\<exists>a[M]. a\<in>A \<and> z=f(a))"
      by (rule_tac rexI[where x="{snd(b) . b \<in> Y}"],auto)
  }
  then
  show ?thesis unfolding strong_replacement_def by simp
qed

lemma Collect_middle: "{p \<in> (\<lambda>x\<in>A. f(x)) \<times> (\<lambda>x\<in>{f(x) . x\<in>A}. g(x)) . snd(fst(p))=fst(snd(p))}
     = { \<langle>\<langle>x,f(x)\<rangle>,\<langle>f(x),g(f(x))\<rangle>\<rangle> . x\<in>A }"
  by (intro equalityI; auto simp:lam_def)

lemma RepFun_middle_del: "{ \<langle>fst(fst(p)),snd(snd(p))\<rangle> . p \<in> { \<langle>\<langle>x,f(x)\<rangle>,\<langle>f(x),g(f(x))\<rangle>\<rangle> . x\<in>A }}
        =  { \<langle>x,g(f(x))\<rangle> . x\<in>A }"
  by auto

lemma lam_replacement_imp_RepFun:
  assumes "lam_replacement(M, f)" "M(A)"
  shows "M({y . x\<in>A , M(y) \<and> y=f(x)})"
proof -
  from assms
  obtain Y where 1:"M(Y)" "\<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x,f(x)\<rangle>)"
    unfolding lam_replacement_def strong_replacement_def
    by auto
  moreover from this
  have "M({snd(b) . b \<in> Y})"
    using transM[OF _ \<open>M(Y)\<close>] lam_replacement_snd lam_replacement_imp_strong_replacement_aux
      RepFun_closed by simp
  moreover
  have "{snd(b) . b \<in> Y} = {y . x\<in>A , M(y) \<and> y=f(x)}" (is "?L=?R")
  proof(intro equalityI subsetI)
    fix x
    assume "x\<in>?L"
    moreover from this
    obtain b where "b\<in>Y" "x=snd(b)" "M(b)"
      using transM[OF _ \<open>M(Y)\<close>] by auto
    moreover from this 1
    obtain a where "a\<in>A" "b=\<langle>a,f(a)\<rangle>" by auto
    moreover from calculation
    have "x=f(a)" by simp
    ultimately show "x\<in>?R"
      by auto
  next
    fix z
    assume "z\<in>?R"
    moreover from this
    obtain a where "a\<in>A" "z=f(a)" "M(a)" "M(f(a))"
      using transM[OF _ \<open>M(A)\<close>]
      by auto
    moreover from calculation this 1
    have "z=snd(\<langle>a,f(a)\<rangle>)" "\<langle>a,f(a)\<rangle> \<in> Y" by auto
    ultimately
    show "z\<in>?L" by force
  qed
  ultimately
  show ?thesis by simp
qed

lemma lam_replacement_product:
  assumes "lam_replacement(M,f)" "lam_replacement(M,g)"
  shows "lam_replacement(M, \<lambda>x. \<langle>f(x),g(x)\<rangle>)"
proof -
  {
    fix A
    let ?Y="{y . x\<in>A , M(y) \<and> y=f(x)}"
    let ?Y'="{y . x\<in>A ,M(y) \<and>  y=\<langle>x,f(x)\<rangle>}"
    let ?Z="{y . x\<in>A , M(y) \<and> y=g(x)}"
    let ?Z'="{y . x\<in>A ,M(y) \<and>  y=\<langle>x,g(x)\<rangle>}"
    have "x\<in>C \<Longrightarrow> y\<in>C \<Longrightarrow> fst(x) = fst(y) \<longrightarrow> M(fst(y)) \<and> M(snd(x)) \<and> M(snd(y))" if "M(C)" for C y x
      using transM[OF _ that] by auto
    moreover
    note assms
    moreover
    assume "M(A)"
    moreover from \<open>M(A)\<close> assms(1)
    have "M(converse(?Y'))" "M(?Y)"
      using lam_replacement_imp_RepFun_Lam lam_replacement_imp_RepFun by auto
    moreover from calculation
    have "M(?Z)" "M(?Z')"
      using lam_replacement_imp_RepFun_Lam lam_replacement_imp_RepFun by auto
    moreover from calculation
    have "M(converse(?Y')\<times>?Z')"
      by simp
    moreover from this
    have "M({p \<in> converse(?Y')\<times>?Z' . snd(fst(p))=fst(snd(p))})" (is "M(?P)")
      using middle_separation by simp
    moreover from calculation
    have "M({ \<langle>snd(fst(p)),\<langle>fst(fst(p)),snd(snd(p))\<rangle>\<rangle> . p\<in>?P })" (is "M(?R)")
      using RepFun_closed[OF lam_replacement_prodRepl[THEN
            lam_replacement_imp_strong_replacement] \<open>M(?P)\<close> ]
      unfolding prodRepl_def by simp
    ultimately
    have "b \<in> ?R \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x,\<langle>f(x),g(x)\<rangle>\<rangle>)" if "M(b)" for b
      using that
      apply(intro iffI) apply(auto)[1]
    proof -
      assume " \<exists>x[M]. x \<in> A \<and> b = \<langle>x, f(x), g(x)\<rangle>"
      moreover from this
      obtain x where "M(x)" "x\<in>A" "b= \<langle>x, \<langle>f(x), g(x)\<rangle>\<rangle>"
        by auto
      moreover from calculation that
      have "M(\<langle>x,f(x)\<rangle>)" "M(\<langle>x,g(x)\<rangle>)" by auto
      moreover from calculation
      have "\<langle>f(x),x\<rangle> \<in> converse(?Y')" "\<langle>x,g(x)\<rangle> \<in> ?Z'" by auto
      moreover from calculation
      have "\<langle>\<langle>f(x),x\<rangle>,\<langle>x,g(x)\<rangle>\<rangle>\<in>converse(?Y')\<times>?Z'" by auto
      moreover from calculation
      have "\<langle>\<langle>f(x),x\<rangle>,\<langle>x,g(x)\<rangle>\<rangle> \<in> ?P"
        (is "?p\<in>?P")
        by auto
      moreover from calculation
      have "b = \<langle>snd(fst(?p)),\<langle>fst(fst(?p)),snd(snd(?p))\<rangle>\<rangle>" by auto
      moreover from calculation
      have "\<langle>snd(fst(?p)),\<langle>fst(fst(?p)),snd(snd(?p))\<rangle>\<rangle>\<in>?R"
        by(rule_tac RepFunI[of ?p ?P], simp)
      ultimately show "b\<in>?R" by simp
    qed
    with \<open>M(?R)\<close>
    have "\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x,\<langle>f(x),g(x)\<rangle>\<rangle>)"
      by (rule_tac rexI[where x="?R"],simp_all)
  }
  with assms
  show ?thesis using lam_replacement_def strong_replacement_def by simp
qed

lemma lam_replacement_hcomp:
  assumes "lam_replacement(M,f)" "lam_replacement(M,g)" "\<forall>x[M]. M(f(x))"
  shows "lam_replacement(M, \<lambda>x. g(f(x)))"
proof -
  {
    fix A
    let ?Y="{y . x\<in>A , y=f(x)}"
    let ?Y'="{y . x\<in>A , y=\<langle>x,f(x)\<rangle>}"
    have "\<forall>x\<in>C. M(\<langle>fst(fst(x)),snd(snd(x))\<rangle>)" if "M(C)" for C
      using transM[OF _ that] by auto
    moreover
    note assms
    moreover
    assume "M(A)"
    moreover from assms
    have eq:"?Y = {y . x\<in>A ,M(y) \<and> y=f(x)}"  "?Y' = {y . x\<in>A ,M(y) \<and> y=\<langle>x,f(x)\<rangle>}"
      using transM[OF _ \<open>M(A)\<close>] by auto
    moreover from \<open>M(A)\<close> assms(1)
    have "M(?Y')" "M(?Y)"
      using lam_replacement_imp_RepFun_Lam lam_replacement_imp_RepFun eq by auto
    moreover from calculation
    have "M({z . y\<in>?Y , M(z) \<and> z=\<langle>y,g(y)\<rangle>})" (is "M(?Z)")
      using lam_replacement_imp_RepFun_Lam by auto
    moreover from calculation
    have "M(?Y'\<times>?Z)"
      by simp
    moreover from this
    have "M({p \<in> ?Y'\<times>?Z . snd(fst(p))=fst(snd(p))})" (is "M(?P)")
      using middle_separation by simp
    moreover from calculation
    have "M({ \<langle>fst(fst(p)),snd(snd(p))\<rangle> . p\<in>?P })" (is "M(?R)")
      using RepFun_closed[OF lam_replacement_middle_del[THEN
            lam_replacement_imp_strong_replacement] \<open>M(?P)\<close>]
      unfolding middle_del_def by simp
    ultimately
    have "b \<in> ?R \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x,g(f(x))\<rangle>)" if "M(b)" for b
      using that assms(3)
      apply(intro iffI) apply(auto)[1]
    proof -
      assume "\<exists>x[M]. x \<in> A \<and> b = \<langle>x, g(f(x))\<rangle>"
      moreover from this
      obtain x where "M(x)" "x\<in>A" "b= \<langle>x, g(f(x))\<rangle>"
        by auto
      moreover from calculation that assms(3)
      have "M(f(x))" "M(g(f(x)))" by auto
      moreover from calculation
      have "\<langle>x,f(x)\<rangle> \<in> ?Y'" by auto
      moreover from calculation
      have "\<langle>f(x),g(f(x))\<rangle>\<in>?Z" by auto
      moreover from calculation
      have "\<langle>\<langle>x,f(x)\<rangle>,\<langle>f(x),g(f(x))\<rangle>\<rangle> \<in> ?P"
        (is "?p\<in>?P")
        by auto
      moreover from calculation
      have "b = \<langle>fst(fst(?p)),snd(snd(?p))\<rangle>" by auto
      moreover from calculation
      have "\<langle>fst(fst(?p)),snd(snd(?p))\<rangle>\<in>?R"
        by(rule_tac RepFunI[of ?p ?P], simp)
      ultimately show "b\<in>?R" by simp
    qed
    with \<open>M(?R)\<close>
    have "\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> b = \<langle>x,g(f(x))\<rangle>)"
      by (rule_tac rexI[where x="?R"],simp_all)
  }
  with assms
  show ?thesis using lam_replacement_def strong_replacement_def by simp
qed

lemma lam_replacement_hcomp2:
  assumes "lam_replacement(M,f)" "lam_replacement(M,g)"
    "\<forall>x[M]. M(f(x))" "\<forall>x[M]. M(g(x))"
    "lam_replacement(M, \<lambda>p. h(fst(p),snd(p)))"
  shows "lam_replacement(M, \<lambda>x. h(f(x),g(x)))"
  using assms lam_replacement_product[of f g]
    lam_replacement_hcomp[of "\<lambda>x. \<langle>f(x), g(x)\<rangle>" "\<lambda>\<langle>x,y\<rangle>. h(x,y)"]
  unfolding split_def by simp

lemma lam_replacement_identity: "lam_replacement(M,\<lambda>x. x)"
proof -
  {
    fix A
    assume "M(A)"
    moreover from this
    have "id(A) = {\<langle>snd(fst(z)),fst(snd(z))\<rangle> . z\<in> {z\<in> (A\<times>A)\<times>(A\<times>A). snd(fst(z)) = fst(snd(z))}}"
      unfolding id_def lam_def
      by(intro equalityI subsetI,simp_all,auto)
    moreover from calculation
    have "M({z\<in> (A\<times>A)\<times>(A\<times>A). snd(fst(z)) = fst(snd(z))})" (is "M(?A')")
      using middle_separation by simp
    moreover from calculation
    have "M({\<langle>snd(fst(z)),fst(snd(z))\<rangle> . z\<in> ?A'})"
      using transM[of _ A]
        lam_replacement_product lam_replacement_hcomp lam_replacement_fst lam_replacement_snd
        lam_replacement_imp_strong_replacement[THEN RepFun_closed]
      by simp_all
    ultimately
    have "M(id(A))" by simp
  }
  then
  show ?thesis using lam_replacement_iff_lam_closed
    unfolding id_def by simp
qed

lemma strong_replacement_separation_aux :
  assumes "strong_replacement(M,\<lambda> x y . y=f(x))" "separation(M,P)"
  shows "strong_replacement(M, \<lambda>x y . P(x) \<and> y=f(x))"
proof -
  {
    fix A
    let ?Q="\<lambda>X. \<forall>b[M]. b \<in> X \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> P(x) \<and> b = f(x))"
    assume "M(A)"
    moreover from this
    have "M({x\<in>A . P(x)})" (is "M(?B)") using assms by simp
    moreover from calculation assms
    obtain Y where "M(Y)" "\<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> ?B \<and> b = f(x))"
      unfolding strong_replacement_def by auto
    then
    have "\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> P(x) \<and> b = f(x))"
      using rexI[of ?Q _ M] by simp
  }
  then
  show ?thesis
    unfolding strong_replacement_def by simp
qed

lemma separation_in:
  assumes "\<forall>x[M]. M(f(x))" "lam_replacement(M,f)"
    "\<forall>x[M]. M(g(x))" "lam_replacement(M,g)"
  shows "separation(M,\<lambda>x . f(x)\<in>g(x))"
proof -
  let ?Z="\<lambda>A. {\<langle>x,\<langle>f(x),g(x)\<rangle>\<rangle>. x\<in>A}"
  have "M(?Z(A))" if "M(A)" for A
    using assms lam_replacement_iff_lam_closed that
      lam_replacement_product[of f g]
    unfolding lam_def
    by auto
  then
  have "M({u\<in>?Z(A) . fst(snd(u)) \<in>snd(snd(u))})" (is "M(?W(A))") if "M(A)" for A
    using that separation_fst_in_snd assms
    by auto
  then
  have "M({fst(u) . u \<in> ?W(A)})" if "M(A)" for A
    using that lam_replacement_imp_strong_replacement[OF lam_replacement_fst,THEN
        RepFun_closed] fst_closed[OF transM]
    by auto
  moreover
  have "{x\<in>A. f(x)\<in>g(x)} = {fst(u) . u\<in>?W(A)}" for A
    by auto
  ultimately
  show ?thesis
    using separation_iff
    by auto
qed

lemma lam_replacement_swap: "lam_replacement(M, \<lambda>x. \<langle>snd(x),fst(x)\<rangle>)"
  using lam_replacement_fst lam_replacement_snd
    lam_replacement_product[of "snd" "fst"] by simp


lemma relation_separation: "separation(M, \<lambda>z. \<exists>x y. z = \<langle>x, y\<rangle>)"
  unfolding separation_def
proof (clarify)
  fix A
  assume "M(A)"
  moreover from this
  have "{z\<in>A. \<exists>x y. z = \<langle>x, y\<rangle>} = {z\<in>A. \<exists>x\<in>domain(A). \<exists>y\<in>range(A). pair(M, x, y, z)}"
    (is "?rel = _")
    by (intro equalityI, auto dest:transM)
      (intro bexI, auto dest:transM simp:Pair_def)
  moreover from calculation
  have "M(?rel)"
    using cartprod_separation[THEN separation_closed, of "domain(A)" "range(A)" A]
    by simp
  ultimately
  show "\<exists>y[M]. \<forall>x[M]. x \<in> y \<longleftrightarrow> x \<in> A \<and> (\<exists>w y. x = \<langle>w, y\<rangle>)"
    by (rule_tac x="{z\<in>A. \<exists>x y. z = \<langle>x, y\<rangle>}" in rexI) auto
qed

lemma separation_Pair:
  assumes "separation(M, \<lambda>y . P(fst(y), snd(y)))"
  shows "separation(M, \<lambda>y. \<exists> u v . y=\<langle>u,v\<rangle> \<and> P(u,v))"
  unfolding separation_def
proof(clarify)
  fix A
  assume "M(A)"
  moreover from this
  have "M({z\<in>A. \<exists>x y. z = \<langle>x, y\<rangle>})" (is "M(?P)")
    using relation_separation by simp
  moreover from this assms
  have "M({z\<in>?P . P(fst(z),snd(z))})"
    by(rule_tac separation_closed,simp_all)
  moreover
  have "{y\<in>A . \<exists> u v . y=\<langle>u,v\<rangle> \<and> P(u,v) } = {z\<in>?P . P(fst(z),snd(z))}"
    by(rule equalityI subsetI,auto)
  moreover from calculation
  have "M({y\<in>A . \<exists> u v . y=\<langle>u,v\<rangle> \<and> P(u,v) })"
    by simp
  ultimately
  show "\<exists>y[M]. \<forall>x[M]. x \<in> y \<longleftrightarrow> x \<in> A \<and> (\<exists>w y. x = \<langle>w, y\<rangle> \<and> P(w,y))"
    by (rule_tac x="{z\<in>A. \<exists>x y. z = \<langle>x, y\<rangle> \<and> P(x,y)}" in rexI) auto
qed

lemma lam_replacement_separation :
  assumes "lam_replacement(M,f)" "separation(M,P)"
  shows "strong_replacement(M, \<lambda>x y . P(x) \<and> y=\<langle>x,f(x)\<rangle>)"
  using strong_replacement_separation_aux assms
  unfolding lam_replacement_def
  by simp

lemmas strong_replacement_separation =
  strong_replacement_separation_aux[OF lam_replacement_imp_strong_replacement]

lemma id_closed: "M(A) \<Longrightarrow> M(id(A))"
  using lam_replacement_identity lam_replacement_iff_lam_closed
  unfolding id_def by simp

lemma lam_replacement_Pair:
  shows "lam_replacement(M, \<lambda>x. \<langle>fst(x), snd(x)\<rangle>)"
  using lam_replacement_product lam_replacement_fst lam_replacement_snd
  by simp

lemma lam_replacement_Upair: "lam_replacement(M, \<lambda>p. Upair(fst(p), snd(p)))"
proof -
  have "(\<not>(\<exists>a b . x = <a,b>)) \<Longrightarrow> fst(x) = 0 \<and> snd(x) = 0" for x
    unfolding fst_def snd_def
    by (simp add:the_0)
  then
  have "Upair(fst(x),snd(x)) = (if (\<exists>w . \<exists> z . x=<w,z>) then (\<Union>x) else ({0}))" for x
    using fst_conv snd_conv Upair_eq_cons
    by (auto simp add:Pair_def)
  moreover
  have "lam_replacement(M, \<lambda>x . (if (\<exists>w . \<exists> z . x=<w,z>) then (\<Union>x) else ({0})))"
    using lam_replacement_Union lam_replacement_constant relation_separation lam_replacement_if
    by simp
  ultimately
  show ?thesis
    using lam_replacement_cong
    by simp
qed

lemma lam_replacement_Un: "lam_replacement(M, \<lambda>p. fst(p) \<union> snd(p))"
  using lam_replacement_Upair lam_replacement_Union
    lam_replacement_hcomp[where g=Union and f="\<lambda>p. Upair(fst(p),snd(p))"]
  unfolding Un_def by simp

lemma lam_replacement_cons: "lam_replacement(M, \<lambda>p. cons(fst(p),snd(p)))"
  using  lam_replacement_Upair
    lam_replacement_hcomp2[of _ _ "(\<union>)"]
    lam_replacement_hcomp2[of fst fst "Upair"]
    lam_replacement_Un lam_replacement_fst lam_replacement_snd
  unfolding cons_def
  by auto

lemma lam_replacement_sing_fun:
  assumes "lam_replacement(M, f)" "\<forall>x[M]. M(f(x))"
  shows "lam_replacement(M, \<lambda>x. {f(x)})"
  using lam_replacement_constant lam_replacement_cons
    lam_replacement_hcomp2[of "f" "\<lambda>_. 0" cons] assms
  by auto

lemma lam_replacement_sing: "lam_replacement(M, \<lambda>x. {x})"
  using lam_replacement_sing_fun lam_replacement_identity
  by simp

lemma lam_replacement_CartProd:
  assumes "lam_replacement(M,f)" "lam_replacement(M,g)"
    "\<forall>x[M]. M(f(x))" "\<forall>x[M]. M(g(x))"
  shows "lam_replacement(M, \<lambda>x. f(x) \<times> g(x))"
proof -
  note rep_closed = lam_replacement_imp_strong_replacement[THEN RepFun_closed]
  {
    fix A
    assume "M(A)"
    moreover
    note transM[OF _ \<open>M(A)\<close>]
    moreover from calculation assms
    have "M({\<langle>x,\<langle>f(x),g(x)\<rangle>\<rangle> . x\<in>A})" (is "M(?A')")
      using lam_replacement_product[THEN lam_replacement_imp_lam_closed[unfolded lam_def]]
      by simp
    moreover from calculation
    have "M(\<Union>{f(x) . x\<in>A})" (is "M(?F)")
      using rep_closed[OF assms(1)] assms(3)
      by simp
    moreover from calculation
    have "M(\<Union>{g(x) . x\<in>A})" (is "M(?G)")
      using rep_closed[OF assms(2)] assms(4)
      by simp
    moreover from calculation
    have "M(?A' \<times> (?F \<times> ?G))" (is "M(?T)")
      by simp
    moreover from this
    have "M({t \<in> ?T . fst(snd(t)) \<in> fst(snd(fst(t))) \<and> snd(snd(t)) \<in> snd(snd(fst(t)))})" (is "M(?Q)")
      using
        lam_replacement_hcomp[OF lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_snd] _ ]
        lam_replacement_hcomp lam_replacement_identity lam_replacement_fst lam_replacement_snd
        separation_in separation_conj
      by simp
    moreover from this
    have "M({\<langle>fst(fst(t)),snd(t)\<rangle> . t\<in>?Q})" (is "M(?R)")
      using rep_closed lam_replacement_product
        lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_fst] lam_replacement_snd
        transM[of _ ?Q]
      by simp
    moreover from calculation
    have "M({\<langle>x,?R``{x}\<rangle> . x\<in>A})"
      using lam_replacement_imp_lam_closed[unfolded lam_def] lam_replacement_sing
        lam_replacement_Image[THEN [5] lam_replacement_hcomp2] lam_replacement_constant[of ?R]
      by simp
    moreover
    have "?R``{x} = f(x)\<times>g(x)" if "x\<in>A" for x
      by(rule equalityI subsetI,force,rule subsetI,rule_tac a="x" in imageI)
        (auto simp:that,(rule_tac rev_bexI[of x],simp_all add:that)+)
    ultimately
    have "M({\<langle>x,f(x) \<times> g(x)\<rangle> . x\<in>A})" by auto
  }
  with assms
  show ?thesis using lam_replacement_iff_lam_closed[THEN iffD2,unfolded lam_def]
    by simp
qed

lemma lam_replacement_RepFun :
  assumes "lam_replacement(M,\<lambda>x . f(fst(x),snd(x)))" "lam_replacement(M,g)"
    "\<forall>x[M].\<forall>y\<in>g(x).M(f(x,y))" "\<forall>x[M].M(g(x))"
  shows "lam_replacement(M,\<lambda>x .  {f(x,z) . z\<in>g(x)})"
proof -
  note rep_closed = lam_replacement_imp_strong_replacement[THEN RepFun_closed]
  from assms
  have "lam_replacement(M,\<lambda>x.{x}\<times>g(x))"
    using lam_replacement_CartProd lam_replacement_sing
    by auto
  moreover from assms
  have "M({f(x,z) . z \<in> g(x)})" if "M(x)" for x
    using that transM[of _ "g(_)"] rep_closed
      lam_replacement_product[OF lam_replacement_fst]
      lam_replacement_snd lam_replacement_identity
      assms(1)[THEN [5] lam_replacement_hcomp2] lam_replacement_constant[of x]
    by simp
  moreover
  have "M(\<lambda>z\<in>A.{f(z,u) . u \<in> g(z)})" if "M(A)" for A
  proof -
    from that assms calculation
    have "M(\<Union>{{x}\<times>g(x) . x\<in>A})" (is "M(?C)")
      using rep_closed transM[of _ A]
      by simp
    with assms \<open>M(A)\<close>
    have "M({\<langle>fst(x),f(fst(x),snd(x))\<rangle> . x \<in>?C})" (is "M(?B)")
      using singleton_closed transM[of _ A] transM[of _ "g(_)"] rep_closed
        lam_replacement_product[OF lam_replacement_fst]
        lam_replacement_hcomp[OF lam_replacement_snd]
      by simp
    with \<open>M(A)\<close>
    have "M({\<langle>x,?B``{x}\<rangle> . x\<in>A})"
      using transM[of _ A] rep_closed
        lam_replacement_product[OF lam_replacement_identity]
        lam_replacement_Image[THEN [5] lam_replacement_hcomp2]
        lam_replacement_constant lam_replacement_sing
      by simp
    moreover
    have "?B``{z} = {f(z,u) . u \<in> g(z)}" if "z\<in>A" for z
      using that
      by(intro equalityI subsetI,auto simp:imageI)
    moreover from this
    have "{\<langle>x,?B``{x}\<rangle> . x\<in>A} = {\<langle>z,{f(z,u) . u \<in> g(z)}\<rangle> . z\<in>A}"
      by auto
    ultimately
    show ?thesis
      unfolding lam_def by auto
  qed
  ultimately
  show ?thesis
    using lam_replacement_iff_lam_closed[THEN iffD2]
    by simp
qed

lemma lam_replacement_Collect :
  assumes "lam_replacement(M,f)" "\<forall>x[M].M(f(x))"
    "separation(M,\<lambda>x . F(fst(x),snd(x)))"
  shows "lam_replacement(M,\<lambda>x. {y\<in>f(x) . F(x,y)})"
proof -
  note rep_closed = lam_replacement_imp_strong_replacement[THEN RepFun_closed]
  from assms
  have 1:"lam_replacement(M,\<lambda>x.{x}\<times>f(x))"
    using lam_replacement_CartProd lam_replacement_sing
    by auto
  have "M({u\<in>f(x) . F(x,u)})" if "M(x)" for x
  proof -
    from assms that
    have "M({u \<in> {x}\<times>f(x) . F(fst(u),snd(u))})" (is "M(?F)")
      by simp
    with assms that
    have "M({snd(u) . u \<in> ?F})"
      using rep_closed transM[of _ "f(x)"] lam_replacement_snd
      by simp
    moreover
    have "{snd(u) . u \<in> ?F} = {u\<in>f(x) . F(x,u)}"
      by auto
    ultimately show ?thesis by simp
  qed
  moreover
  have "M(\<lambda>z\<in>A.{y \<in> f(z) . F(z,y)})" if "M(A)" for A
  proof -
    from 1 that assms
    have "M(\<Union>{{x}\<times>f(x) . x\<in>A})" (is "M(?C)")
      using rep_closed transM[of _ A]
      by simp
    moreover from this assms
    have "M({p \<in> ?C . F(fst(p),snd(p))})" (is "M(?B)")
      by(rule_tac separation_closed,simp_all)
    with \<open>M(A)\<close>
    have "M({\<langle>x,?B``{x}\<rangle> . x\<in>A})"
      using transM[of _ A] rep_closed
        lam_replacement_product[OF lam_replacement_identity]
        lam_replacement_Image[THEN [5] lam_replacement_hcomp2]
        lam_replacement_constant lam_replacement_sing
      by simp
    moreover
    have "?B``{z} = {u\<in>f(z) . F(z,u)}" if "z\<in>A" for z
      using that
      by(intro equalityI subsetI,auto simp:imageI)
    moreover from this
    have "{\<langle>x,?B``{x}\<rangle> . x\<in>A} = {\<langle>z,{u\<in>f(z) . F(z,u)}\<rangle> . z\<in>A}"
      by auto
    ultimately
    show ?thesis
      unfolding lam_def by auto
  qed
  ultimately
  show ?thesis
    using lam_replacement_iff_lam_closed[THEN iffD2]
    by simp
qed


lemma separation_eq:
  assumes "\<forall>x[M]. M(f(x))" "lam_replacement(M,f)"
    "\<forall>x[M]. M(g(x))" "lam_replacement(M,g)"
  shows "separation(M,\<lambda>x . f(x) = g(x))"
proof -
  let ?Z="\<lambda>A. {\<langle>x,\<langle>f(x),\<langle>g(x),x\<rangle>\<rangle>\<rangle>. x\<in>A}"
  let ?Y="\<lambda>A. {\<langle>\<langle>x,f(x)\<rangle>,\<langle>g(x),x\<rangle>\<rangle>. x\<in>A}"
  note sndsnd = lam_replacement_hcomp[OF lam_replacement_snd lam_replacement_snd]
  note fstsnd = lam_replacement_hcomp[OF lam_replacement_snd lam_replacement_fst]
  note sndfst = lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_snd]
  have "M(?Z(A))" if "M(A)" for A
    using assms lam_replacement_iff_lam_closed that
      lam_replacement_product[OF assms(2)
        lam_replacement_product[OF assms(4) lam_replacement_identity]]
    unfolding lam_def
    by auto
  moreover
  have "?Y(A) = {\<langle>\<langle>fst(x), fst(snd(x))\<rangle>, fst(snd(snd(x))), snd(snd(snd(x)))\<rangle> . x \<in> ?Z(A)}" for A
    by auto
  moreover from calculation
  have "M(?Y(A))" if "M(A)" for A
    using
      lam_replacement_imp_strong_replacement[OF
        lam_replacement_product[OF
          lam_replacement_product[OF lam_replacement_fst fstsnd]
          lam_replacement_product[OF
            lam_replacement_hcomp[OF sndsnd lam_replacement_fst]
            lam_replacement_hcomp[OF lam_replacement_snd sndsnd]
            ]
          ], THEN RepFun_closed,simplified,of "?Z(A)"]
      fst_closed[OF transM] snd_closed[OF transM] that
    by auto
  then
  have "M({u\<in>?Y(A) . snd(fst(u)) = fst(snd(u))})" (is "M(?W(A))") if "M(A)" for A
    using that middle_separation assms
    by auto
  then
  have "M({fst(fst(u)) . u \<in> ?W(A)})" if "M(A)" for A
    using that lam_replacement_imp_strong_replacement[OF
        lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_fst], THEN RepFun_closed]
      fst_closed[OF transM]
    by auto
  moreover
  have "{x\<in>A. f(x) = g(x)} = {fst(fst(u)) . u\<in>?W(A)}" for A
    by auto
  ultimately
  show ?thesis
    using separation_iff by auto
qed
lemma separation_comp :
  assumes "separation(M,P)" "lam_replacement(M,f)" "\<forall>x[M]. M(f(x))"
  shows "separation(M,\<lambda>x. P(f(x)))"
  unfolding separation_def
proof(clarify)
  fix A
  assume "M(A)"
  let ?B="{f(a) . a \<in> A}"
  let ?C="A\<times>{b\<in>?B . P(b)}"
  note \<open>M(A)\<close>
  moreover from calculation
  have "M(?C)"
    using lam_replacement_imp_strong_replacement assms RepFun_closed transM[of _ A]
    by simp
  moreover from calculation
  have "M({p\<in>?C . f(fst(p)) = snd(p)})" (is "M(?Prod)")
    using assms separation_eq lam_replacement_fst lam_replacement_snd
      lam_replacement_hcomp
    by simp
  moreover from calculation
  have "M({fst(p) . p\<in>?Prod})" (is "M(?L)")
    using lam_replacement_imp_strong_replacement lam_replacement_fst RepFun_closed
      transM[of _ ?Prod]
    by simp
  moreover
  have "?L = {z\<in>A . P(f(z))}"
    by(intro equalityI subsetI,auto)
  ultimately
  show " \<exists>y[M]. \<forall>z[M]. z \<in> y \<longleftrightarrow> z \<in> A \<and> P(f(z))"
    by (rule_tac x="?L" in rexI,simp_all)
qed

lemma lam_replacement_domain: "lam_replacement(M,domain)"
proof -
  have 1:"{fst(z) . z\<in> {u\<in>x . (\<exists> a b. u = <a,b>)}} =domain(x)" for x
    unfolding domain_def
    by (intro equalityI subsetI,auto,rule_tac x="<xa,y>" in bexI,auto)
  moreover
  have "lam_replacement(M,\<lambda> x .{fst(z) . z\<in> {u\<in>x . (\<exists> a b. u = <a,b>)}})"
    using lam_replacement_hcomp lam_replacement_snd lam_replacement_fst
snd_closed[OF transM] fst_closed[OF transM] lam_replacement_identity
relation_separation relation_separation[THEN separation_comp,where f=snd]
lam_replacement_Collect
    by(rule_tac lam_replacement_RepFun,simp_all)
  ultimately
  show ?thesis
    using lam_replacement_cong
    by auto
qed

lemma separation_in_domain : "M(a) \<Longrightarrow> separation(M, \<lambda>x. a\<in>domain(x))"
  using lam_replacement_domain lam_replacement_constant separation_in
  by auto


lemma separation_all:
  assumes "separation(M, \<lambda>x . P(fst(fst(x)),snd(x)))"
    "lam_replacement(M,f)" "lam_replacement(M,g)"
    "\<forall>x[M]. M(f(x))" "\<forall>x[M]. M(g(x))"
  shows "separation(M, \<lambda>z. \<forall>x\<in>f(z). P(g(z),x))"
  unfolding separation_def
proof(clarify)
  note rep_closed = lam_replacement_imp_strong_replacement[THEN RepFun_closed]
  note lr_fs = lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_snd]
  fix A
  assume "M(A)"
  with assms
  have "M({f(x) . x\<in>A})" (is "M(?F)") "M({<g(x),f(x)> . x\<in>A})" (is "M(?G)")
    using rep_closed transM[of _ A]
      lam_replacement_product lam_replacement_imp_lam_closed
    unfolding lam_def
    by auto
  let ?B="\<Union>?F"
  let ?C="?G\<times>?B"
  note \<open>M(A)\<close> \<open>M(?F)\<close> \<open>M(?G)\<close>
  moreover from calculation
  have "M(?C)"
    by simp
  moreover from calculation
  have "M({p\<in>?C . P(fst(fst(p)),snd(p)) \<and> snd(p)\<in>snd(fst(p))})" (is "M(?Prod)")
    using assms separation_conj separation_in lam_replacement_fst lam_replacement_snd
      lam_replacement_hcomp
    by simp
  moreover from calculation
  have "M({z\<in>?G . snd(z)=?Prod``{z}})" (is "M(?L)")
    using separation_eq
      lam_replacement_constant[of ?Prod] lam_replacement_constant[of 0]
      lam_replacement_hcomp[OF _ lam_replacement_sing]
      lam_replacement_Image[THEN [5] lam_replacement_hcomp2]
      lam_replacement_identity lam_replacement_snd
    by simp
  moreover from calculation assms
  have "M({x\<in>A . <g(x),f(x)> \<in> ?L})" (is "M(?N)")
    using lam_replacement_product lam_replacement_constant
    by (rule_tac separation_closed,rule_tac separation_in,auto)
  moreover from calculation
  have "?N = {z\<in>A . \<forall>x\<in>f(z). P(g(z),x)}"
  proof -
    have "P(g(z),x)" if "z\<in>A" "x\<in>f(z)" "f(z) = ?Prod``{<g(z),f(z)>}" for z x
      using that
      by(rule_tac imageE[of x ?Prod "{<g(z),f(z)>}"],simp_all)
    moreover
    have "f(z) = ?Prod `` {<g(z),f(z)>}" if "z\<in>A" "\<forall>x\<in>f(z). P(g(z), x)" for z
      using that
      by force
    ultimately
    show ?thesis
      by auto
  qed
  ultimately
  show " \<exists>y[M]. \<forall>z[M]. z \<in> y \<longleftrightarrow> z \<in> A \<and> (\<forall>x\<in>f(z) . P(g(z),x))"
    by (rule_tac x="?N" in rexI,simp_all)
qed

lemma separation_ex:
  assumes "separation(M, \<lambda>x . P(fst(fst(x)),snd(x)))"
    "lam_replacement(M,f)" "lam_replacement(M,g)"
    "\<forall>x[M]. M(f(x))" "\<forall>x[M]. M(g(x))"
  shows "separation(M, \<lambda>z. \<exists>x\<in>f(z). P(g(z),x))"
  unfolding separation_def
proof(clarify)
  note rep_closed = lam_replacement_imp_strong_replacement[THEN RepFun_closed]
  note lr_fs = lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_snd]
  fix A
  assume "M(A)"
  with assms
  have "M({f(x) . x\<in>A})" (is "M(?F)") "M({<g(x),f(x)> . x\<in>A})" (is "M(?G)")
    using rep_closed transM[of _ A]
      lam_replacement_product lam_replacement_imp_lam_closed
    unfolding lam_def
    by auto
  let ?B="\<Union>?F"
  let ?C="?G\<times>?B"
  note \<open>M(A)\<close> \<open>M(?F)\<close> \<open>M(?G)\<close>
  moreover from calculation
  have "M(?C)"
    by simp
  moreover from calculation
  have "M({p\<in>?C . P(fst(fst(p)),snd(p)) \<and> snd(p)\<in>snd(fst(p))})" (is "M(?Prod)")
    using assms separation_conj separation_in lam_replacement_fst lam_replacement_snd
      lam_replacement_hcomp
    by simp
  moreover from calculation
  have "M({z\<in>?G . 0\<noteq>?Prod``{z}})" (is "M(?L)")
    using separation_eq  separation_neg
      lam_replacement_constant[of ?Prod] lam_replacement_constant[of 0]
      lam_replacement_hcomp[OF _ lam_replacement_sing]
      lam_replacement_Image[THEN [5] lam_replacement_hcomp2]
      lam_replacement_identity
    by simp
  moreover from calculation assms
  have "M({x\<in>A . <g(x),f(x)> \<in> ?L})" (is "M(?N)")
    using lam_replacement_product lam_replacement_constant
    by (rule_tac separation_closed,rule_tac separation_in,auto)
  moreover from calculation
  have "?N = {z\<in>A . \<exists>x\<in>f(z). P(g(z),x)}"
    by(intro equalityI subsetI,simp_all,force) (rule ccontr,force)
  ultimately
  show " \<exists>y[M]. \<forall>z[M]. z \<in> y \<longleftrightarrow> z \<in> A \<and> (\<exists>x\<in>f(z) . P(g(z),x))"
    by (rule_tac x="?N" in rexI,simp_all)
qed

lemma lam_replacement_converse: "lam_replacement(M,converse)"
proof-
  note lr_Un = lam_replacement_Union[THEN [2] lam_replacement_hcomp]
  note lr_fs = lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_snd]
  note lr_ff = lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_fst]
  note lr_ss = lam_replacement_hcomp[OF lam_replacement_snd lam_replacement_snd]
  note lr_sf = lam_replacement_hcomp[OF  lr_ff lam_replacement_snd]
  note lr_fff = lam_replacement_hcomp[OF lam_replacement_fst lr_ff]
  note lr_f4 = lam_replacement_hcomp[OF lr_ff lr_ff]
  have eq:"converse(x) = {\<langle>snd(y),fst(y)\<rangle> . y \<in> {z \<in> x. \<exists> u \<in>\<Union>\<Union>x . \<exists>v\<in>\<Union>\<Union>x . z=<u,v>}}" for x
    unfolding converse_def
    by(intro equalityI subsetI,auto,rename_tac a b,rule_tac x="<a,b>" in bexI,simp_all)
     (auto simp : Pair_def)
  have "M(x) \<Longrightarrow> M({z \<in> x. \<exists> u \<in>\<Union>\<Union>x . \<exists>v\<in>\<Union>\<Union>x . z=<u,v>})" for x
    using lam_replacement_identity lr_Un[OF lr_Un] lr_Un lr_Un[OF lam_replacement_Union]
      lam_replacement_snd lr_ff lam_replacement_fst lam_replacement_hcomp lr_fff
      lam_replacement_product[OF lr_sf lam_replacement_snd] lr_f4
      lam_replacement_hcomp[OF lr_f4 lam_replacement_snd] separation_eq
      lam_replacement_constant
    by(rule_tac separation_closed,rule_tac separation_ex,rule_tac separation_ex,simp_all)
  moreover
  have sep:"separation(M, \<lambda>x. \<exists>u\<in>\<Union>\<Union>fst(x). \<exists>v\<in>\<Union>\<Union>fst(x). snd(x) = \<langle>u, v\<rangle>)"
    using lam_replacement_identity lr_Un[OF lr_Un] lr_Un
      lam_replacement_snd lr_ff lam_replacement_fst lam_replacement_hcomp lr_fff
      lam_replacement_product[OF lr_sf lam_replacement_snd]
      lam_replacement_hcomp[OF lr_f4 lam_replacement_snd] separation_eq
    by(rule_tac separation_ex,rule_tac separation_ex,simp_all)
  moreover from calculation
  have "lam_replacement(M, \<lambda>x. {z \<in> x . \<exists>u\<in>\<Union>\<Union>x. \<exists>v\<in>\<Union>\<Union>x. z = \<langle>u, v\<rangle>})"
    using lam_replacement_identity
    by(rule_tac lam_replacement_Collect,simp_all)
  ultimately
  have 1:"lam_replacement(M, \<lambda>x . {\<langle>snd(y),fst(y)\<rangle> . y \<in> {z \<in> x. \<exists>u \<in>\<Union>\<Union>x . \<exists>v\<in>\<Union>\<Union>x. z=<u,v>}})"
    using lam_replacement_product lam_replacement_fst lam_replacement_hcomp
      lam_replacement_identity lr_ff lr_ss
      lam_replacement_snd lam_replacement_identity sep
    by(rule_tac lam_replacement_RepFun,simp_all,force dest:transM)
  with eq[symmetric]
  show ?thesis
    by(rule_tac lam_replacement_cong[OF 1],simp_all)
qed

lemma lam_replacement_Diff: "lam_replacement(M, \<lambda>x . fst(x) - snd(x))"
proof -
  have eq:"X - Y = {x\<in>X . x\<notin>Y}" for X Y
    by auto
  moreover
  have "lam_replacement(M, \<lambda>x . {y \<in> fst(x) . y\<notin>snd(x)})"
    using  lam_replacement_fst lam_replacement_hcomp
      lam_replacement_snd lam_replacement_identity separation_in separation_neg
    by(rule_tac lam_replacement_Collect,simp_all)
  then
  show ?thesis
    by(rule_tac lam_replacement_cong,auto,subst eq[symmetric],simp)
qed

lemma lam_replacement_range : "lam_replacement(M,range)"
  unfolding range_def
  using lam_replacement_hcomp[OF lam_replacement_converse lam_replacement_domain]
  by auto

lemma separation_in_range : "M(a) \<Longrightarrow> separation(M, \<lambda>x. a\<in>range(x))"
  using lam_replacement_range lam_replacement_constant separation_in
  by auto

lemmas tag_replacement = lam_replacement_constant[unfolded lam_replacement_def]

lemma tag_lam_replacement : "M(X) \<Longrightarrow> lam_replacement(M,\<lambda>x. <X,x>)"
  using lam_replacement_product[OF lam_replacement_constant] lam_replacement_identity
  by simp

lemma strong_lam_replacement_imp_lam_replacement_RepFun :
  assumes  "strong_replacement(M,\<lambda> x z . P(fst(x),snd(x)) \<and> z=\<langle>x,f(fst(x),snd(x))\<rangle>)"
  "lam_replacement(M,g)"
  "\<And>A y . M(y) \<Longrightarrow> M(A) \<Longrightarrow> \<forall>x\<in>A. P(y,x) \<longrightarrow> M(f(y,x))"
  "\<forall>x[M]. M(g(x))"
  "separation(M, \<lambda>x. P(fst(x),snd(x)))"
  shows "lam_replacement(M, \<lambda>x. {y . r\<in> g(x) , P(x,r) \<and> y=f(x,r)}) "
proof -
  note rep_closed = lam_replacement_imp_strong_replacement[THEN RepFun_closed]
  moreover
  have "{f(x, xa) . xa \<in> {xa \<in> g(x) . P(x, xa)}} = {y . z \<in> g(x), P(x, z) \<and> y = f(x, z)}" for x
    by(intro equalityI subsetI,auto)
  moreover from assms
  have 0:"M({xa \<in> g(x) . P(x, xa)})" if "M(x)" for x
    using that separation_closed assms(5)[THEN separation_comp,OF tag_lam_replacement]
    by simp
  moreover from assms
  have 1:"lam_replacement(M,\<lambda>x.{x}\<times>{u\<in>g(x) . P(x,u)})" (is "lam_replacement(M,\<lambda>x.?R(x))")
    using separation_closed assms(5)[THEN separation_comp,OF tag_lam_replacement]
    by(rule_tac lam_replacement_CartProd[OF lam_replacement_sing lam_replacement_Collect],simp_all)
  moreover from assms
  have "M({y . z\<in>g(x) , P(x,z) \<and> y=f(x,z)})" (is "M(?Q(x))") if "M(x)" for x
    using that transM[of _ "g(_)"]
      separation_closed assms(5)[THEN separation_comp,OF tag_lam_replacement]
      assms(3)[of "x" "g(x)"] strong_lam_replacement_imp_strong_replacement
    by simp
  moreover
  have "M(\<lambda>z\<in>A.{f(z,r) . r \<in> {u\<in> g(z) . P(z,u)}})" if "M(A)" for A
  proof -
    from that assms calculation
    have "M(\<Union>{?R(x) . x\<in>A})" (is "M(?C)")
      using transM[of _ A] rep_closed
      by simp
    moreover from assms \<open>M(A)\<close>
    have "x \<in> {y} \<times> {x \<in> g(y) . P(y, x)} \<Longrightarrow> M(x) \<and> M(f(fst(x),snd(x)))" if "y\<in>A" for y x
      using assms(3)[of "y" "g(y)"] transM[of _ A] transM[of _ "g(y)"] that
      by force
    moreover from this
    have "\<exists>y\<in>A . x \<in> {y} \<times> {x \<in> g(y) . P(y, x)} \<Longrightarrow> M(x) \<and> M(f(fst(x),snd(x)))" for x
      by auto
    moreover note assms \<open>M(A)\<close>
    ultimately
    have "M({z . x\<in>?C , P(fst(x),snd(x)) \<and> z = \<langle>x,f(fst(x),snd(x))\<rangle>})" (is "M(?B)")
      using singleton_closed transM[of _ A] transM[of _ "g(_)"] rep_closed
        lam_replacement_product[OF lam_replacement_fst]
        lam_replacement_hcomp[OF lam_replacement_snd] transM[OF _ 0]
      by(rule_tac strong_replacement_closed,simp_all)
    then
    have "M({\<langle>fst(fst(x)),snd(x)\<rangle> . x\<in>?B})" (is "M(?D)")
      using rep_closed transM[of _ ?B]
        lam_replacement_product[OF
          lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_fst]
          lam_replacement_snd]
      by simp
    with \<open>M(A)\<close>
    have "M({\<langle>x,?D``{x}\<rangle> . x\<in>A})"
      using transM[of _ A] rep_closed
        lam_replacement_product[OF lam_replacement_identity]
        lam_replacement_Image[THEN [5] lam_replacement_hcomp2]
        lam_replacement_constant lam_replacement_sing
      by simp
    moreover from calculation
    have "?D``{z} = {f(z,r) . r \<in> {u\<in> g(z) . P(z,u)}}" if "z\<in>A" for z
      using that
      by (intro equalityI subsetI,auto,intro imageI,force,auto)
    moreover from this
    have "{\<langle>x,?D``{x}\<rangle> . x\<in>A} = {\<langle>z,{f(z,r) . r \<in> {u\<in> g(z) . P(z,u)}}\<rangle> . z\<in>A}"
      by auto
    ultimately
    show ?thesis
      unfolding lam_def by auto
  qed
  ultimately
  show ?thesis
    using lam_replacement_iff_lam_closed[THEN iffD2]
    by simp
qed

lemma lam_replacement_Collect' :
  assumes "M(A)" "separation(M,\<lambda>p . F(fst(p),snd(p)))"
  shows "lam_replacement(M,\<lambda>x. {y\<in>A . F(x,y)})"
  using assms lam_replacement_constant
  by(rule_tac lam_replacement_Collect, simp_all)

lemma lam_replacement_id2: "lam_replacement(M, \<lambda>x. \<langle>x, x\<rangle>)"
  using lam_replacement_identity lam_replacement_product[of "\<lambda>x. x" "\<lambda>x. x"]
  by simp

lemmas id_replacement = lam_replacement_id2[unfolded lam_replacement_def]

lemma lam_replacement_apply2:"lam_replacement(M, \<lambda>p. fst(p) ` snd(p))"
  using lam_replacement_fst lam_replacement_sing_fun[OF lam_replacement_snd]
    lam_replacement_Image lam_replacement_Union
    lam_replacement_hcomp[of _ Union] lam_replacement_hcomp2[of _ _ "(``)"]
  unfolding apply_def
  by simp

lemma lam_replacement_apply:"M(S) \<Longrightarrow> lam_replacement(M, \<lambda>x.  S ` x)"
  using lam_replacement_constant[of S] lam_replacement_identity
    lam_replacement_apply2[THEN [5] lam_replacement_hcomp2]
  by simp

lemma apply_replacement:"M(S) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = S ` x)"
  using lam_replacement_apply lam_replacement_imp_strong_replacement by simp

lemma lam_replacement_id_const: "M(b) \<Longrightarrow> lam_replacement(M, \<lambda>x. \<langle>x, b\<rangle>)"
  using lam_replacement_identity lam_replacement_constant
    lam_replacement_product[of "\<lambda>x. x" "\<lambda>x. b"] by simp

lemmas pospend_replacement = lam_replacement_id_const[unfolded lam_replacement_def]

lemma lam_replacement_const_id: "M(b) \<Longrightarrow> lam_replacement(M, \<lambda>z. \<langle>b, z\<rangle>)"
  using lam_replacement_identity lam_replacement_constant
    lam_replacement_product[of "\<lambda>x. b" "\<lambda>x. x"] by simp

lemmas prepend_replacement = lam_replacement_const_id[unfolded lam_replacement_def]

lemma lam_replacement_apply_const_id: "M(f) \<Longrightarrow> M(z) \<Longrightarrow>
      lam_replacement(M, \<lambda>x. f ` \<langle>z, x\<rangle>)"
  using lam_replacement_const_id[of z] lam_replacement_apply
    lam_replacement_hcomp[of "\<lambda>x. \<langle>z, x\<rangle>"] by simp

lemmas apply_replacement2 = lam_replacement_apply_const_id[unfolded lam_replacement_def]

lemma lam_replacement_Inl: "lam_replacement(M, Inl)"
  using lam_replacement_identity lam_replacement_constant
    lam_replacement_product[of "\<lambda>x. 0" "\<lambda>x. x"]
  unfolding Inl_def by simp

lemma lam_replacement_Inr: "lam_replacement(M, Inr)"
  using lam_replacement_identity lam_replacement_constant
    lam_replacement_product[of "\<lambda>x. 1" "\<lambda>x. x"]
  unfolding Inr_def by simp

lemmas Inl_replacement1 = lam_replacement_Inl[unfolded lam_replacement_def]

lemma lam_replacement_Diff': "M(X) \<Longrightarrow> lam_replacement(M, \<lambda>x. x - X)"
  using lam_replacement_Diff[THEN [5] lam_replacement_hcomp2]
    lam_replacement_constant lam_replacement_identity
  by simp

lemmas Pair_diff_replacement = lam_replacement_Diff'[unfolded lam_replacement_def]

lemma diff_Pair_replacement: "M(p) \<Longrightarrow> strong_replacement(M, \<lambda>x y . y=\<langle>x,x-{p}\<rangle>)"
  using Pair_diff_replacement by simp

lemma swap_replacement:"strong_replacement(M, \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>x,y\<rangle>. \<langle>y, x\<rangle>)(x)\<rangle>)"
  using lam_replacement_swap unfolding lam_replacement_def split_def by simp

lemma lam_replacement_Un_const:"M(b) \<Longrightarrow> lam_replacement(M, \<lambda>x. x \<union> b)"
  using lam_replacement_Un lam_replacement_hcomp2[of _ _ "(\<union>)"]
    lam_replacement_constant[of b] lam_replacement_identity by simp

lemmas tag_union_replacement = lam_replacement_Un_const[unfolded lam_replacement_def]

lemma lam_replacement_csquare: "lam_replacement(M,\<lambda>p. \<langle>fst(p) \<union> snd(p), fst(p), snd(p)\<rangle>)"
  using lam_replacement_Un lam_replacement_fst lam_replacement_snd
  by (fast intro: lam_replacement_product lam_replacement_hcomp2)

lemma csquare_lam_replacement:"strong_replacement(M, \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>x,y\<rangle>. \<langle>x \<union> y, x, y\<rangle>)(x)\<rangle>)"
  using lam_replacement_csquare unfolding split_def lam_replacement_def .

lemma lam_replacement_assoc:"lam_replacement(M,\<lambda>x. \<langle>fst(fst(x)), snd(fst(x)), snd(x)\<rangle>)"
  using lam_replacement_fst lam_replacement_snd
  by (force intro: lam_replacement_product lam_replacement_hcomp)

lemma assoc_replacement:"strong_replacement(M, \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>\<langle>x,y\<rangle>,z\<rangle>. \<langle>x, y, z\<rangle>)(x)\<rangle>)"
  using lam_replacement_assoc unfolding split_def lam_replacement_def .

lemma lam_replacement_prod_fun: "M(f) \<Longrightarrow> M(g) \<Longrightarrow> lam_replacement(M,\<lambda>x. \<langle>f ` fst(x), g ` snd(x)\<rangle>)"
  using lam_replacement_fst lam_replacement_snd
  by (force intro: lam_replacement_product lam_replacement_hcomp lam_replacement_apply)

lemma prod_fun_replacement:"M(f) \<Longrightarrow> M(g) \<Longrightarrow>
  strong_replacement(M, \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>w,y\<rangle>. \<langle>f ` w, g ` y\<rangle>)(x)\<rangle>)"
  using lam_replacement_prod_fun unfolding split_def lam_replacement_def .

lemma separation_subset:
  assumes "\<forall>x[M]. M(f(x))" "lam_replacement(M,f)"
    "\<forall>x[M]. M(g(x))" "lam_replacement(M,g)"
  shows "separation(M,\<lambda>x . f(x) \<subseteq> g(x))"
proof -
  have "f(x) \<subseteq> g(x) \<longleftrightarrow> f(x)\<union>g(x) = g(x)" for x
    using subset_Un_iff by simp
  moreover from assms
  have "separation(M,\<lambda>x . f(x)\<union>g(x) = g(x))"
    using separation_eq lam_replacement_Un lam_replacement_hcomp2
    by simp
  ultimately
  show ?thesis
    using separation_cong[THEN iffD1] by auto
qed

lemma lam_replacement_twist: "lam_replacement(M,\<lambda>\<langle>\<langle>x,y\<rangle>,z\<rangle>. \<langle>x,y,z\<rangle>)"
  using lam_replacement_fst lam_replacement_snd
    lam_replacement_Pair[THEN [5] lam_replacement_hcomp2,
      of "\<lambda>x. snd(fst(x))" "\<lambda>x. snd(x)", THEN [2] lam_replacement_Pair[
        THEN [5] lam_replacement_hcomp2, of "\<lambda>x. fst(fst(x))"]]
    lam_replacement_hcomp unfolding split_def by simp

lemma twist_closed[intro,simp]: "M(x) \<Longrightarrow> M((\<lambda>\<langle>\<langle>x,y\<rangle>,z\<rangle>. \<langle>x,y,z\<rangle>)(x))"
  unfolding split_def by simp

lemma lam_replacement_vimage :
  shows "lam_replacement(M, \<lambda>x. fst(x)-``snd(x))"
  unfolding vimage_def using
    lam_replacement_Image[THEN [5] lam_replacement_hcomp2]
      lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_converse] lam_replacement_snd
  by simp

lemma lam_replacement_vimage_sing: "lam_replacement(M, \<lambda>p. fst(p) -`` {snd(p)})"
  using lam_replacement_snd lam_replacement_sing_fun
    lam_replacement_vimage[THEN [5] lam_replacement_hcomp2] lam_replacement_fst
  by simp

lemma lam_replacement_vimage_sing_fun: "M(f) \<Longrightarrow> lam_replacement(M, \<lambda>x. f -`` {x})"
  using lam_replacement_vimage_sing[THEN [5] lam_replacement_hcomp2] lam_replacement_constant[of f]
      lam_replacement_identity
  by simp

lemma lam_replacement_image_sing_fun: "M(f) \<Longrightarrow> lam_replacement(M, \<lambda>x. f `` {x})"
  using lam_replacement_Image[THEN [5] lam_replacement_hcomp2] lam_replacement_constant[of f]
      lam_replacement_sing
  by simp

lemma converse_apply_projs: "\<forall>x[M]. \<Union> (fst(x) -`` {snd(x)}) = converse(fst(x)) ` (snd(x))"
  using converse_apply_eq by auto

lemma lam_replacement_converse_app: "lam_replacement(M, \<lambda>p. converse(fst(p)) ` snd(p))"
  using lam_replacement_cong[OF _ converse_apply_projs]
    lam_replacement_hcomp[OF lam_replacement_vimage_sing lam_replacement_Union]
  by simp

lemmas cardinal_lib_assms4 = lam_replacement_vimage_sing_fun[unfolded lam_replacement_def]

lemma lam_replacement_sing_const_id:
  "M(x) \<Longrightarrow> lam_replacement(M, \<lambda>y. {\<langle>x, y\<rangle>})"
  using lam_replacement_const_id[of x] lam_replacement_sing_fun
  by simp

lemma tag_singleton_closed: "M(x) \<Longrightarrow> M(z) \<Longrightarrow> M({{\<langle>z, y\<rangle>} . y \<in> x})"
  using RepFun_closed lam_replacement_imp_strong_replacement lam_replacement_sing_const_id
    transM[of _ x]
  by simp

lemma separation_ball:
  assumes "separation(M, \<lambda>y. f(fst(y),snd(y)))" "M(X)"
  shows "separation(M, \<lambda>y. \<forall>u\<in>X. f(y,u))"
  unfolding separation_def
proof(clarify)
  fix A
  assume "M(A)"
  moreover
  note \<open>M(X)\<close>
  moreover from calculation
  have "M(A\<times>X)"
    by simp
  then
  have "M({p \<in> A\<times>X . f(fst(p),snd(p))})" (is "M(?P)")
    using assms(1)
    by auto
  moreover from calculation
  have "M({a\<in>A . ?P``{a} = X})" (is "M(?A')")
    using separation_eq lam_replacement_image_sing_fun[of "?P"] lam_replacement_constant
    by simp
  moreover
  have "f(a,x)" if "a\<in>?A'" and "x\<in>X" for a x
  proof -
    from that
    have "a\<in>A" "?P``{a}=X"
      by auto
    then
    have "x\<in>?P``{a}"
      using that by simp
    then
    show ?thesis using image_singleton_iff by simp
  qed
  moreover from this
  have "\<forall>a[M]. a \<in> ?A' \<longleftrightarrow> a \<in> A \<and> (\<forall>x\<in>X. f(a, x))"
    using image_singleton_iff
    by auto
  with \<open>M(?A')\<close>
  show "\<exists>y[M]. \<forall>a[M]. a \<in> y \<longleftrightarrow> a \<in> A \<and> (\<forall>x\<in>X. f(a, x))"
    by (rule_tac x="?A'" in rexI,simp_all)
qed

lemma separation_bex:
  assumes "separation(M, \<lambda>y. f(fst(y),snd(y)))" "M(X)"
  shows "separation(M, \<lambda>y. \<exists>u\<in>X. f(y,u))"
  unfolding separation_def
proof(clarify)
  fix A
  assume "M(A)"
  moreover
  note \<open>M(X)\<close>
  moreover from calculation
  have "M(A\<times>X)"
    by simp
  then
  have "M({p \<in> A\<times>X . f(fst(p),snd(p))})" (is "M(?P)")
    using assms(1)
    by auto
  moreover from calculation
  have "M({a\<in>A . ?P``{a} \<noteq> 0})" (is "M(?A')")
    using separation_eq lam_replacement_image_sing_fun[of "?P"] lam_replacement_constant
      separation_neg
    by simp
  moreover from this
  have "\<forall>a[M]. a \<in> ?A' \<longleftrightarrow> a \<in> A \<and> (\<exists>x\<in>X. f(a, x))"
    using image_singleton_iff
    by auto
  with \<open>M(?A')\<close>
  show "\<exists>y[M]. \<forall>a[M]. a \<in> y \<longleftrightarrow> a \<in> A \<and> (\<exists>x\<in>X. f(a, x))"
    by (rule_tac x="?A'" in rexI,simp_all)
qed

lemma lam_replacement_Lambda:
  assumes "lam_replacement(M, \<lambda>y. b(fst(y), snd(y)))"
    "\<forall>w[M]. \<forall>y[M]. M(b(w, y))" "M(W)"
  shows "lam_replacement(M, \<lambda>x. \<lambda>w\<in>W. b(x, w))"
  using assms lam_replacement_constant lam_replacement_product lam_replacement_snd
    lam_replacement_RepFun transM[of _ W]
  unfolding lam_def
  by simp

lemma lam_replacement_apply_Pair:
  assumes "M(y)"
  shows "lam_replacement(M, \<lambda>x. y ` \<langle>fst(x), snd(x)\<rangle>)"
  using assms lam_replacement_constant lam_replacement_Pair
    lam_replacement_apply2[THEN [5] lam_replacement_hcomp2]
  by auto

lemma lam_replacement_apply_fst_snd:
  shows "lam_replacement(M, \<lambda>w. fst(w) ` fst(snd(w)) ` snd(snd(w)))"
  using lam_replacement_fst lam_replacement_snd lam_replacement_hcomp
    lam_replacement_apply2[THEN [5] lam_replacement_hcomp2]
  by auto

lemma lam_replacement_RepFun_apply :
  assumes "M(f)"
  shows "lam_replacement(M, \<lambda>x . {f`y . y \<in> x})"
  using assms  lam_replacement_identity lam_replacement_RepFun
    lam_replacement_hcomp lam_replacement_snd lam_replacement_apply
  by(rule_tac lam_replacement_RepFun,auto dest:transM)

lemma separation_snd_in_fst: "separation(M, \<lambda>x. snd(x) \<in> fst(x))"
  using separation_in lam_replacement_fst lam_replacement_snd
  by auto

lemma lam_replacement_if_mem:
  "lam_replacement(M, \<lambda>x. if snd(x) \<in> fst(x) then 1 else 0)"
  using separation_snd_in_fst
    lam_replacement_constant lam_replacement_if
  by auto

lemma lam_replacement_Lambda_apply_fst_snd:
  assumes "M(X)"
  shows "lam_replacement(M, \<lambda>x. \<lambda>w\<in>X. x ` fst(w) ` snd(w))"
  using assms lam_replacement_apply_fst_snd lam_replacement_Lambda
  by simp

lemma lam_replacement_Lambda_apply_Pair:
  assumes "M(X)" "M(y)"
  shows "lam_replacement(M, \<lambda>x. \<lambda>w\<in>X. y ` \<langle>x, w\<rangle>)"
  using assms lam_replacement_apply_Pair lam_replacement_Lambda
  by simp

lemma lam_replacement_Lambda_if_mem:
  assumes "M(X)"
  shows "lam_replacement(M, \<lambda>x. \<lambda>xa\<in>X. if xa \<in> x then 1 else 0)"
  using assms lam_replacement_if_mem lam_replacement_Lambda
  by simp

lemma case_closed :
  assumes "\<forall>x[M]. M(f(x))" "\<forall>x[M]. M(g(x))"
  shows "\<forall>x[M]. M(case(f,g,x))"
  unfolding case_def split_def cond_def
  using assms by simp

lemma separation_fst_equal : "M(a) \<Longrightarrow> separation(M,\<lambda>x . fst(x)=a)"
  using separation_eq lam_replacement_fst lam_replacement_constant
  by auto

lemma lam_replacement_case :
  assumes "lam_replacement(M,f)" "lam_replacement(M,g)"
    "\<forall>x[M]. M(f(x))" "\<forall>x[M]. M(g(x))"
  shows "lam_replacement(M, \<lambda>x . case(f,g,x))"
  unfolding case_def split_def cond_def
  using lam_replacement_if separation_fst_equal
    lam_replacement_hcomp[of "snd" g]
    lam_replacement_hcomp[of "snd" f]
    lam_replacement_snd assms
  by simp

lemma Pi_replacement1: "M(x) \<Longrightarrow> M(y) \<Longrightarrow>  strong_replacement(M, \<lambda>ya z. ya \<in> y \<and> z = {\<langle>x, ya\<rangle>})"
  using lam_replacement_imp_strong_replacement
    strong_replacement_separation[OF lam_replacement_sing_const_id[of x],where P="\<lambda>x . x \<in>y"]
    separation_in_constant
  by simp

lemma surj_imp_inj_replacement1:
  "M(f) \<Longrightarrow> M(x) \<Longrightarrow> strong_replacement(M, \<lambda>y z. y \<in> f -`` {x} \<and> z = {\<langle>x, y\<rangle>})"
  using Pi_replacement1 vimage_closed singleton_closed
  by simp

lemmas domain_replacement = lam_replacement_domain[unfolded lam_replacement_def]

lemma domain_replacement_simp: "strong_replacement(M, \<lambda>x y. y=domain(x))"
  using lam_replacement_domain lam_replacement_imp_strong_replacement by simp

lemma un_Pair_replacement: "M(p) \<Longrightarrow> strong_replacement(M, \<lambda>x y . y = x\<union>{p})"
  using lam_replacement_Un_const[THEN lam_replacement_imp_strong_replacement] by simp

lemma diff_replacement: "M(X) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = x - X)"
  using lam_replacement_Diff'[THEN lam_replacement_imp_strong_replacement] by simp

lemma lam_replacement_succ:
  "lam_replacement(M,\<lambda>z . succ(z))"
  unfolding succ_def
  using lam_replacement_hcomp2[of "\<lambda>x. x" "\<lambda>x. x" cons]
    lam_replacement_cons lam_replacement_identity
  by simp

lemma lam_replacement_hcomp_Least:
  assumes "lam_replacement(M, g)" "lam_replacement(M,\<lambda>x. \<mu> i. x\<in>F(i,x))"
    "\<forall>x[M]. M(g(x))" "\<And>x i. M(x) \<Longrightarrow> i \<in> F(i, x) \<Longrightarrow> M(i)"
  shows "lam_replacement(M,\<lambda>x. \<mu> i. g(x)\<in>F(i,g(x)))"
  using assms
  by (rule_tac lam_replacement_hcomp[of _ "\<lambda>x. \<mu> i. x\<in>F(i,x)"])
    (auto intro:Least_closed')

lemma domain_mem_separation: "M(A) \<Longrightarrow> separation(M, \<lambda>x . domain(x)\<in>A)"
  using separation_in lam_replacement_constant lam_replacement_domain
  by auto

lemma domain_eq_separation: "M(p) \<Longrightarrow> separation(M, \<lambda>x . domain(x) = p)"
  using separation_eq lam_replacement_domain lam_replacement_constant
  by auto

lemma lam_replacement_Int:
  shows "lam_replacement(M, \<lambda>x. fst(x) \<inter> snd(x))"
proof -
  have "A\<inter>B = (A\<union>B) - ((A- B) \<union> (B-A))" (is "_=?f(A,B)")for A B
    by auto
  then
  show ?thesis
    using lam_replacement_cong
      lam_replacement_Diff[THEN[5] lam_replacement_hcomp2]
      lam_replacement_Un[THEN[5] lam_replacement_hcomp2]
      lam_replacement_fst lam_replacement_snd
    by simp
qed

lemma restrict_eq_separation': "M(B) \<Longrightarrow> \<forall>A[M]. separation(M, \<lambda>y. \<exists>x[M]. x\<in>A \<and> y = \<langle>x, restrict(x, B)\<rangle>)"
proof(clarify)
  fix A
  have "restrict(r,B) = r \<inter> (B \<times> range(r))" for r
    unfolding restrict_def by(rule equalityI subsetI,auto)
  moreover
  assume "M(A)" "M(B)"
  moreover from this
  have "separation(M, \<lambda>y. \<exists>x\<in>A. y = \<langle>x, x \<inter> (B \<times> range(x))\<rangle>)"
    using lam_replacement_Int[THEN[5] lam_replacement_hcomp2]
      lam_replacement_Pair[THEN[5] lam_replacement_hcomp2]
    using lam_replacement_fst lam_replacement_snd lam_replacement_constant
      lam_replacement_hcomp lam_replacement_range lam_replacement_identity
      lam_replacement_CartProd separation_bex separation_eq
    by simp_all
  ultimately
  show "separation(M, \<lambda>y. \<exists>x[M]. x\<in>A \<and> y = \<langle>x, restrict(x, B)\<rangle>)"
    by simp
qed

lemmas lam_replacement_restrict' = lam_replacement_restrict[OF restrict_eq_separation']

lemma restrict_strong_replacement: "M(A) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y=restrict(x,A))"
  using lam_replacement_restrict restrict_eq_separation'
    lam_replacement_imp_strong_replacement
  by simp

lemma restrict_eq_separation: "M(r) \<Longrightarrow> M(p) \<Longrightarrow> separation(M, \<lambda>x . restrict(x,r) = p)"
  using separation_eq lam_replacement_restrict' lam_replacement_constant
  by auto

lemma separation_equal_fst2 : "M(a) \<Longrightarrow> separation(M,\<lambda>x . fst(fst(x))=a)"
  using separation_eq lam_replacement_hcomp lam_replacement_fst lam_replacement_constant
  by auto

lemma separation_equal_apply: "M(f) \<Longrightarrow> M(a) \<Longrightarrow> separation(M,\<lambda>x. f`x=a)"
  using separation_eq lam_replacement_apply[of f] lam_replacement_constant
  by auto

lemma lam_apply_replacement: "M(A) \<Longrightarrow> M(f) \<Longrightarrow> lam_replacement(M, \<lambda>x . \<lambda>n\<in>A. f ` \<langle>x, n\<rangle>)"
  using lam_replacement_Lambda lam_replacement_hcomp[OF _ lam_replacement_apply[of f]] lam_replacement_Pair
  by simp

\<comment> \<open>We need a tactic to deal with composition of replacements!\<close>
lemma lam_replacement_comp :
  "lam_replacement(M, \<lambda>x . fst(x) O snd(x))"
proof -
  note lr_fs = lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_snd]
  note lr_ff = lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_fst]
  note lr_ss = lam_replacement_hcomp[OF lam_replacement_snd lam_replacement_snd]
  note lr_sf = lam_replacement_hcomp[OF lam_replacement_snd lam_replacement_fst]
  note lr_fff = lam_replacement_hcomp[OF lam_replacement_fst lr_ff]
  have eq:"R O S =
      {xz \<in> domain(S) \<times> range(R) .
        \<exists>y\<in>range(S)\<inter>domain(R) . \<langle>fst(xz),y\<rangle>\<in>S \<and> \<langle>y,snd(xz)\<rangle>\<in>R}" for R S
    unfolding comp_def
    by(intro equalityI subsetI,auto)
  moreover
  have "lam_replacement(M, \<lambda>x . {xz \<in> domain(snd(x)) \<times> range(fst(x)) .
        \<exists>y\<in>range(snd(x))\<inter>domain(fst(x)) . \<langle>fst(xz),y\<rangle>\<in>snd(x) \<and> \<langle>y,snd(xz)\<rangle>\<in>fst(x)})"
    using lam_replacement_CartProd lam_replacement_hcomp
      lam_replacement_range lam_replacement_domain lam_replacement_fst lam_replacement_snd
      lam_replacement_identity lr_fs lr_ff lr_ss lam_replacement_product
      lam_replacement_Int[THEN [5] lam_replacement_hcomp2]
      lam_replacement_hcomp[OF lr_ff lam_replacement_domain]
      lam_replacement_hcomp[OF lr_fs lam_replacement_range]
      lam_replacement_hcomp[OF lr_ff lr_ff]
      lam_replacement_hcomp[OF lr_ff lr_ss]
      lam_replacement_hcomp[OF lr_ff lr_sf]
      lr_fff
      lam_replacement_hcomp[OF lr_fff lam_replacement_snd ]
      separation_ex separation_conj separation_in
    by(rule_tac lam_replacement_Collect,simp_all,rule_tac separation_ex,rule_tac separation_conj,auto)
  ultimately
  show ?thesis
    by(rule_tac lam_replacement_cong,auto,subst eq[symmetric],rule_tac comp_closed,auto)
qed

lemma lam_replacement_comp':
  "M(f) \<Longrightarrow> M(g) \<Longrightarrow> lam_replacement(M, \<lambda>x . f O x O g)"
  using lam_replacement_comp[THEN [5] lam_replacement_hcomp2,
      OF lam_replacement_constant lam_replacement_comp,
      THEN [5] lam_replacement_hcomp2] lam_replacement_constant
    lam_replacement_identity by simp

lemma RepFun_SigFun_closed: "M(x)\<Longrightarrow> M(z) \<Longrightarrow> M({{\<langle>z, u\<rangle>} . u \<in> x})"
  using lam_replacement_sing_const_id lam_replacement_imp_strong_replacement RepFun_closed
    transM[of _ x] singleton_in_M_iff pair_in_M_iff
  by simp

\<comment> \<open>Gives the orthogonal of \<^term>\<open>x\<close> with respect to the relation \<^term>\<open>Q\<close>.\<close>
lemma separation_orthogonal: "M(x) \<Longrightarrow> M(Q) \<Longrightarrow> separation(M, \<lambda>a .  \<forall>s\<in>x. \<langle>s, a\<rangle> \<in> Q)"
  using separation_in[OF _
      lam_replacement_hcomp2[OF _ _ _ _ lam_replacement_Pair] _
      lam_replacement_constant]
    separation_ball lam_replacement_hcomp lam_replacement_fst lam_replacement_snd
  by simp_all

lemma separation_Transset: "separation(M,Transset)"
  unfolding Transset_def
  using separation_subset lam_replacement_fst lam_replacement_snd
    lam_replacement_hcomp lam_replacement_identity
  by(rule_tac separation_all,auto)


lemma separation_Ord: "separation(M,Ord)"
  unfolding Ord_def
  using  separation_Transset
    separation_comp separation_Transset lam_replacement_snd lam_replacement_identity
  by(rule_tac separation_conj,auto,rule_tac separation_all,auto)

lemma ord_iso_separation: "M(A) \<Longrightarrow> M(r) \<Longrightarrow> M(s) \<Longrightarrow>
      separation(M, \<lambda>f. \<forall>x\<in>A. \<forall>y\<in>A. \<langle>x, y\<rangle> \<in> r \<longleftrightarrow> \<langle>f ` x, f ` y\<rangle> \<in> s)"
  using
    lam_replacement_Pair[THEN[5] lam_replacement_hcomp2]
    lam_replacement_apply2[THEN[5] lam_replacement_hcomp2]
    lam_replacement_hcomp lam_replacement_fst lam_replacement_snd
    lam_replacement_identity lam_replacement_constant
    separation_in separation_ball[of _ A] separation_iff'
  by simp

lemma separation_dist: "separation(M, \<lambda> x . \<exists>a. \<exists>b . x=\<langle>a,b\<rangle> \<and> a\<noteq>b)"
  using separation_Pair separation_neg separation_eq lam_replacement_fst lam_replacement_snd
  by simp

lemma separation_imp_lam_closed:
  assumes "\<forall>x\<in>A. F(x) \<in> B" "separation(M, \<lambda>\<langle>x,y\<rangle>. F(x) = y)"
    "M(A)" "M(B)"
  shows "M(\<lambda>x\<in>A. F(x))"
proof -
  from \<open>\<forall>x\<in>A. F(x) \<in> B\<close>
  have "(\<lambda>x\<in>A. F(x)) \<subseteq> A\<times>B"
    using times_subset_iff fun_is_rel[OF lam_funtype, of A F]
    by auto
  moreover from this
  have "(\<lambda>x\<in>A. F(x)) = {\<langle>x,y\<rangle> \<in> A \<times> B. F(x) = y}"
    unfolding lam_def by force
  moreover
  note \<open>M(A)\<close> \<open>M(B)\<close> \<open>separation(M, \<lambda>\<langle>x,y\<rangle>. F(x) = y)\<close>
  moreover from this
  have "M({\<langle>x,y\<rangle> \<in> A \<times> B. F(x) = y})"
    by simp
  ultimately
  show ?thesis
    unfolding lam_def
    by auto
qed

lemma curry_closed :
  assumes "M(f)" "M(A)" "M(B)"
  shows "M(curry(A,B,f))"
  using assms lam_replacement_apply_const_id
    lam_apply_replacement lam_replacement_iff_lam_closed
  unfolding curry_def
  by auto

end \<comment> \<open>\<^locale>\<open>M_replacement\<close>\<close>

definition
  RepFun_cons :: "i\<Rightarrow>i\<Rightarrow>i" where
  "RepFun_cons(x,y) \<equiv> RepFun(x, \<lambda>z. {\<langle>y,z\<rangle>})"

context M_replacement
begin

lemma lam_replacement_RepFun_cons'':
  shows "lam_replacement(M, \<lambda>x . RepFun_cons(fst(x),snd(x)))"
  unfolding RepFun_cons_def
  using lam_replacement_fst fst_closed snd_closed lam_replacement_product
lam_replacement_snd lam_replacement_hcomp lam_replacement_sing_fun
   transM[OF _ fst_closed]
lam_replacement_RepFun[of "\<lambda> x z . {<snd(x),z>}" "fst"]
  by simp

lemma RepFun_cons_replacement: "lam_replacement(M, \<lambda>p. RepFun(fst(p), \<lambda>x. {\<langle>snd(p),x\<rangle>}))"
  using lam_replacement_RepFun_cons''
  unfolding RepFun_cons_def
  by simp

lemma lam_replacement_Sigfun:
  assumes "lam_replacement(M,f)" "\<forall>y[M]. M(f(y))"
  shows "lam_replacement(M, \<lambda>x. Sigfun(x,f))"
  using assms lam_replacement_Union lam_replacement_sing_fun lam_replacement_Pair
       tag_singleton_closed transM[of _ "f(_)"] lam_replacement_hcomp[of _ Union]
       lam_replacement_RepFun
  unfolding Sigfun_def
  by simp

lemma phrank_repl:
  assumes
    "M(f)"
  shows
    "strong_replacement(M, \<lambda>x y. y = succ(f`x))"
  using assms lam_replacement_succ lam_replacement_apply
    lam_replacement_imp_strong_replacement lam_replacement_hcomp
  by auto

lemma lam_replacement_Powapply_rel:
  assumes "\<forall>A[M]. separation(M, \<lambda>y. \<exists>x[M]. x \<in> A \<and> y = \<langle>x, Pow_rel(M,x)\<rangle>)"
    "M(f)"
  shows
    "lam_replacement(M, Powapply_rel(M,f))"
  using assms lam_replacement_Pow_rel lam_replacement_apply[THEN lam_replacement_hcomp]
  unfolding Powapply_rel_def
  by auto

lemmas Powapply_rel_replacement = lam_replacement_Powapply_rel[THEN
    lam_replacement_imp_strong_replacement]

lemma surj_imp_inj_replacement2:
  "M(f) \<Longrightarrow> strong_replacement(M, \<lambda>x z. z = Sigfun(x, \<lambda>y. f -`` {y}))"
  using lam_replacement_imp_strong_replacement lam_replacement_Sigfun
    lam_replacement_vimage_sing_fun
  by simp

lemma lam_replacement_Pi: "M(y) \<Longrightarrow> lam_replacement(M, \<lambda>x. \<Union>xa\<in>y. {\<langle>x, xa\<rangle>})"
  using  lam_replacement_constant lam_replacement_Sigfun[unfolded Sigfun_def,of "\<lambda>x. y"]
  by (simp)

lemma Pi_replacement2: "M(y) \<Longrightarrow> strong_replacement(M, \<lambda>x z. z = (\<Union>xa\<in>y. {\<langle>x, xa\<rangle>}))"
  using lam_replacement_Pi[THEN lam_replacement_imp_strong_replacement, of y]
  by simp

lemma if_then_Inj_replacement:
  shows "M(A) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, if x \<in> A then Inl(x) else Inr(x)\<rangle>)"
  using lam_replacement_if lam_replacement_Inl lam_replacement_Inr separation_in_constant
  unfolding lam_replacement_def
  by simp

lemma lam_if_then_replacement:
  "M(b) \<Longrightarrow>
    M(a) \<Longrightarrow> M(f) \<Longrightarrow> strong_replacement(M, \<lambda>y ya. ya = \<langle>y, if y = a then b else f ` y\<rangle>)"
  using lam_replacement_if lam_replacement_apply lam_replacement_constant
    separation_equal
  unfolding lam_replacement_def
  by simp

lemma if_then_replacement:
  "M(A) \<Longrightarrow> M(f) \<Longrightarrow> M(g) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, if x \<in> A then f ` x else g ` x\<rangle>)"
  using lam_replacement_if lam_replacement_apply[of f] lam_replacement_apply[of g]
    separation_in_constant
  unfolding lam_replacement_def
  by simp

lemma ifx_replacement:
  "M(f) \<Longrightarrow>
    M(b) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, if x \<in> range(f) then converse(f) ` x else b\<rangle>)"
  using lam_replacement_if lam_replacement_apply lam_replacement_constant
    separation_in_constant
  unfolding lam_replacement_def
  by simp

lemma if_then_range_replacement2:
  "M(A) \<Longrightarrow> M(C) \<Longrightarrow> strong_replacement(M, \<lambda>x y. y = \<langle>x, if x = Inl(A) then C else x\<rangle>)"
  using lam_replacement_if lam_replacement_constant lam_replacement_identity
    separation_equal
  unfolding lam_replacement_def
  by simp

lemma if_then_range_replacement:
  "M(u) \<Longrightarrow>
    M(f) \<Longrightarrow>
    strong_replacement
     (M,
      \<lambda>z y. y = \<langle>z, if z = u then f ` 0 else if z \<in> range(f) then f ` succ(converse(f) ` z) else z\<rangle>)"
  using lam_replacement_if separation_equal separation_in_constant
    lam_replacement_constant lam_replacement_identity
    lam_replacement_succ lam_replacement_apply
    lam_replacement_hcomp[of "\<lambda>x. converse(f)`x" "succ"]
    lam_replacement_hcomp[of "\<lambda>x. succ(converse(f)`x)" "\<lambda>x . f`x"]
  unfolding lam_replacement_def
  by simp

lemma Inl_replacement2:
  "M(A) \<Longrightarrow>
    strong_replacement(M, \<lambda>x y. y = \<langle>x, if fst(x) = A then Inl(snd(x)) else Inr(x)\<rangle>)"
  using lam_replacement_if separation_fst_equal
    lam_replacement_hcomp[of "snd" "Inl"]
    lam_replacement_Inl lam_replacement_Inr lam_replacement_snd
  unfolding lam_replacement_def
  by simp

lemma case_replacement1:
  "strong_replacement(M, \<lambda>z y. y = \<langle>z, case(Inr, Inl, z)\<rangle>)"
  using lam_replacement_case lam_replacement_Inl lam_replacement_Inr
  unfolding lam_replacement_def
  by simp

lemma case_replacement2:
  "strong_replacement(M, \<lambda>z y. y = \<langle>z, case(case(Inl, \<lambda>y. Inr(Inl(y))), \<lambda>y. Inr(Inr(y)), z)\<rangle>)"
  using lam_replacement_case lam_replacement_hcomp
    case_closed[of Inl "\<lambda>x. Inr(Inl(x))"]
    lam_replacement_Inl lam_replacement_Inr
  unfolding lam_replacement_def
  by simp

lemma case_replacement4:
  "M(f) \<Longrightarrow> M(g) \<Longrightarrow> strong_replacement(M, \<lambda>z y. y = \<langle>z, case(\<lambda>w. Inl(f ` w), \<lambda>y. Inr(g ` y), z)\<rangle>)"
  using lam_replacement_case lam_replacement_hcomp
    lam_replacement_Inl lam_replacement_Inr lam_replacement_apply
  unfolding lam_replacement_def
  by simp

lemma case_replacement5:
  "strong_replacement(M, \<lambda>x y. y = \<langle>x, (\<lambda>\<langle>x,z\<rangle>. case(\<lambda>y. Inl(\<langle>y, z\<rangle>), \<lambda>y. Inr(\<langle>y, z\<rangle>), x))(x)\<rangle>)"
  unfolding split_def case_def cond_def
  using lam_replacement_if separation_equal_fst2
    lam_replacement_snd lam_replacement_Inl lam_replacement_Inr
    lam_replacement_hcomp[OF
      lam_replacement_product[OF
        lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_snd]]]
  unfolding lam_replacement_def
  by simp

end \<comment> \<open>\<^locale>\<open>M_replacement\<close>\<close>

locale M_Pi_replacement = M_Pi + M_replacement

begin
lemma curry_rel_exp :
  assumes "M(f)" "M(A)" "M(B)" "M(C)" "f \<in> A \<times> B \<rightarrow> C"
  shows "curry(A,B,f) \<in> A \<rightarrow>\<^bsup>M\<^esup> (B \<rightarrow>\<^bsup>M\<^esup> C)"
  using assms transM[of _ A] lam_closed[OF apply_replacement2]
    lam_replacement_apply_const_id
    lam_apply_replacement lam_replacement_iff_lam_closed
  unfolding curry_def
  by (intro lam_type mem_function_space_rel_abs[THEN iffD2],auto)

end \<comment> \<open>\<^locale>\<open>M_Pi_replacement\<close>\<close>

\<comment> \<open>To be used in the relativized treatment of Cohen posets\<close>
definition
  \<comment> \<open>"domain collect F"\<close>
  dC_F :: "i \<Rightarrow> i \<Rightarrow> i" where
  "dC_F(A,d) \<equiv> {p \<in> A. domain(p) = d }"

definition
  \<comment> \<open>"domain restrict SepReplace Y"\<close>
  drSR_Y :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i" where
  "drSR_Y(B,D,A,x) \<equiv> {y . r\<in>A , restrict(r,B) = x \<and> y = domain(r) \<and> domain(r) \<in> D}"

lemma drSR_Y_equality: "drSR_Y(B,D,A,x) = { dr\<in>D . (\<exists>r\<in>A . restrict(r,B) = x \<and> dr=domain(r)) }"
  unfolding drSR_Y_def by auto

context M_replacement
begin

lemma separation_restrict_eq_dom_eq:"\<forall>x[M].separation(M, \<lambda>dr. \<exists>r\<in>A . restrict(r,B) = x \<and> dr=domain(r))"
  if "M(A)" and "M(B)" for A B
  using that
    separation_eq[OF _
      lam_replacement_fst _
      lam_replacement_hcomp[OF lam_replacement_snd lam_replacement_domain ]]
    separation_eq[OF _
      lam_replacement_hcomp[OF lam_replacement_snd lam_replacement_restrict'] _
      lam_replacement_constant]
  by(clarify,rule_tac separation_bex[OF _ \<open>M(A)\<close>],rule_tac separation_conj,simp_all)


lemma separation_is_insnd_restrict_eq_dom : "separation(M, \<lambda>p. (\<exists>r\<in>A. restrict(r, B) = fst(p) \<and> snd(p) = domain(r)))"
  if "M(B)" "M(D)" "M(A)" for A B D
  using that lam_replacement_fst lam_replacement_snd
    separation_eq lam_replacement_hcomp lam_replacement_domain
    lam_replacement_hcomp[OF _ lam_replacement_restrict']
  by( rule_tac separation_bex[OF _ \<open>M(A)\<close>],rule_tac separation_conj,simp_all)

lemma lam_replacement_drSR_Y:
  assumes "M(B)" "M(D)" "M(A)"
  shows "lam_replacement(M, drSR_Y(B,D,A))"
  using lam_replacement_cong[OF lam_replacement_Collect'[OF _ separation_is_insnd_restrict_eq_dom]]
    assms drSR_Y_equality separation_restrict_eq_dom_eq
  by simp

lemma drSR_Y_closed:
  assumes "M(B)" "M(D)" "M(A)" "M(f)"
  shows "M(drSR_Y(B,D,A,f))"
  using assms drSR_Y_equality lam_replacement_Collect'[OF \<open>M(D)\<close>]
    assms drSR_Y_equality separation_is_insnd_restrict_eq_dom separation_restrict_eq_dom_eq
  by simp

lemma lam_if_then_apply_replacement: "M(f) \<Longrightarrow> M(v) \<Longrightarrow> M(u) \<Longrightarrow>
     lam_replacement(M, \<lambda>x. if f ` x = v then f ` u else f ` x)"
  using lam_replacement_if separation_equal_apply lam_replacement_constant lam_replacement_apply
  by simp

lemma  lam_if_then_apply_replacement2: "M(f) \<Longrightarrow> M(m) \<Longrightarrow> M(y) \<Longrightarrow>
     lam_replacement(M, \<lambda>z . if f ` z = m then y else f ` z)"
  using lam_replacement_if separation_equal_apply lam_replacement_constant lam_replacement_apply
  by simp

lemma lam_if_then_replacement2: "M(A) \<Longrightarrow> M(f) \<Longrightarrow>
     lam_replacement(M, \<lambda>x . if x \<in> A then f ` x else x)"
  using lam_replacement_if separation_in_constant lam_replacement_identity lam_replacement_apply
  by simp

lemma lam_if_then_replacement_apply: "M(G) \<Longrightarrow> lam_replacement(M, \<lambda>x. if M(x) then G ` x else 0)"
  using lam_replacement_if separation_in_constant lam_replacement_identity lam_replacement_apply
    lam_replacement_constant[of 0] separation_univ
  by simp

lemma lam_replacement_dC_F:
  assumes "M(A)"
  shows "lam_replacement(M, dC_F(A))"
proof -
  have "separation(M, \<lambda>p.  domain(snd(p)) = fst(p))" if "M(A)" for A
    using separation_eq that
      lam_replacement_hcomp lam_replacement_fst lam_replacement_snd lam_replacement_domain
    by simp_all
  then
  show ?thesis
    unfolding dC_F_def
    using assms lam_replacement_Collect'[of A "\<lambda> d x . domain(x) = d"]
      separation_eq[OF _ lam_replacement_domain _ lam_replacement_constant]
    by simp
  qed

lemma dCF_closed:
  assumes "M(A)" "M(f)"
  shows "M(dC_F(A,f))"
  unfolding dC_F_def
  using assms lam_replacement_Collect'[of A "\<lambda> d x . domain(x) = d"]
    separation_eq[OF _ lam_replacement_domain _ lam_replacement_constant]
  by simp

lemma lam_replacement_Collect_ball_Pair:
  assumes  "M(G)" "M(Q)"
  shows "lam_replacement(M, \<lambda>x . {a \<in> G . \<forall>s\<in>x. \<langle>s, a\<rangle> \<in> Q})"
proof -
  have "separation(M, \<lambda>p. (\<forall>s\<in>fst(p). \<langle>s, snd(p)\<rangle> \<in> Q))"
         using separation_in assms lam_replacement_identity
      lam_replacement_constant lam_replacement_hcomp[OF lam_replacement_fst
        lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_snd]]
      lam_replacement_snd lam_replacement_fst
      lam_replacement_hcomp[OF lam_replacement_fst lam_replacement_fst]
         by(rule_tac separation_all,simp_all,rule_tac separation_in,simp_all,rule_tac lam_replacement_product[of "snd" "\<lambda>x . snd(fst(fst(x)))"],simp_all)
       then
       show ?thesis
    using assms lam_replacement_Collect'
    by simp_all
qed

lemma surj_imp_inj_replacement3:
  assumes  "M(G)" "M(Q)" "M(x)"
  shows "strong_replacement(M, \<lambda>y z. y \<in> {a \<in> G . \<forall>s\<in>x. \<langle>s, a\<rangle> \<in> Q} \<and> z = {\<langle>x, y\<rangle>})"
proof -
  from assms
  have "separation(M, \<lambda>z. \<forall>s\<in>x. \<langle>s, z\<rangle> \<in> Q)"
    using lam_replacement_swap lam_replacement_constant separation_in separation_ball
    by simp
  with assms
  show ?thesis
    using separation_in_constant lam_replacement_sing_const_id[of x] separation_conj
    by(rule_tac strong_replacement_separation,simp_all)
qed

lemmas replacements = Pair_diff_replacement id_replacement tag_replacement
  pospend_replacement prepend_replacement
  Inl_replacement1  diff_Pair_replacement
  swap_replacement tag_union_replacement csquare_lam_replacement
  assoc_replacement prod_fun_replacement
  cardinal_lib_assms4  domain_replacement
  apply_replacement
  un_Pair_replacement restrict_strong_replacement diff_replacement
  if_then_Inj_replacement lam_if_then_replacement if_then_replacement
  ifx_replacement if_then_range_replacement2 if_then_range_replacement
  Inl_replacement2
  case_replacement1 case_replacement2 case_replacement4 case_replacement5

lemma zermelo_separation: "M(Q) \<Longrightarrow> M(f) \<Longrightarrow> separation(M, \<lambda>X. Q \<union> f `` X \<subseteq> X)"
  using lam_replacement_identity lam_replacement_Un[THEN [5] lam_replacement_hcomp2]
    lam_replacement_constant lam_replacement_Image[THEN [5] lam_replacement_hcomp2]
    separation_subset
  by simp

end \<comment> \<open>\<^locale>\<open>M_replacement\<close>\<close>

subsection\<open>Some basic replacement lemmas\<close>

lemma (in M_trans) strong_replacement_conj:
  assumes "\<And>A. M(A) \<Longrightarrow> univalent(M,A,P)" "strong_replacement(M,P)"
    "separation(M, \<lambda>x. \<exists>b[M]. Q(x,b) \<and> P(x,b))"
  shows "strong_replacement(M, \<lambda>x z. Q(x,z) \<and> P(x,z))"
proof -
  {
    fix A
    assume "M(A)"
    with \<open>separation(M, \<lambda>x. \<exists>b[M]. Q(x,b) \<and> P(x,b))\<close>
    have "M({x\<in>A. \<exists>b[M]. Q(x,b) \<and> P(x,b)})"
      by simp
    with \<open>M(_) \<Longrightarrow> univalent(M,{x\<in>A. \<exists>b[M]. Q(x,b) \<and> P(x,b)}, P)\<close> \<open>strong_replacement(M, P)\<close>
    have "\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> {x\<in>A. \<exists>b[M]. Q(x,b) \<and> P(x,b)} \<and> P(x, b))"
      unfolding strong_replacement_def by blast
    then
    obtain Y where "\<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> {x\<in>A. \<exists>b[M]. Q(x,b) \<and> P(x,b)} \<and> P(x, b))" "M(Y)"
      by blast
    with \<open>M(A)\<close> \<open>M(A) \<Longrightarrow> univalent(M,A,P)\<close>
    have "\<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> Q(x, b) \<and> P(x, b))"
      unfolding univalent_def by auto
    with \<open>M(Y)\<close>
    have "\<exists>Y[M]. \<forall>b[M]. b \<in> Y \<longleftrightarrow> (\<exists>x[M]. x \<in> A \<and> Q(x, b) \<and> P(x, b))"
      by auto
  }
  then
  show ?thesis
    unfolding strong_replacement_def by simp
qed

lemma strong_replacement_iff_bounded_M:
  "strong_replacement(M,P) \<longleftrightarrow> strong_replacement(M,\<lambda> x z . M(z) \<and> M(x) \<and> P(x,z))"
  unfolding strong_replacement_def by auto

end
