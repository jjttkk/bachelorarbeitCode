(*
  File:      Elimination_Of_Repeated_Factors/ERF_Perfect_Field_Factorization.thy
  Authors:   Katharina Kreuzer (TU München)
             Manuel Eberl (University of Innsbruck)

  Auxiliary computations for the correctness of the ERF algorithm.
*)

theory ERF_Perfect_Field_Factorization

imports ERF_Library

begin
text \<open>Here we subsume properties of the factorization of a polynomial and its derivative in 
perfect fields. 
There are two main examples for perfect fields: fields with characteristic $0$ and finite fields
(i.e.\ $\mathbb{F}_q[x]$ where $q=p^n$, $n\in\mathbb{N}$ and $p$ prime). 
For fields with characteristic $0$, most of the lemmas below become trivial. But in the case of 
finite fields we get interesting results.

Since fields are not instantiated with gcd, we need the additional type class constraint \<open>field_gcd\<close>.\<close>
locale perfect_field_poly_factorization =
  fixes e :: "'e :: {perfect_field, field_gcd} itself"
    and f :: "'e poly"
    and p :: nat
  assumes p_def: "p = CHAR('e)"
    and deg: "degree f \<noteq> 0"
begin
text \<open>Definitions to shorten the terms.\<close>
definition fm where "fm = normalize f"
definition fac where "fac = prime_factorization fm"
definition fac_set where "fac_set = prime_factors fm"
definition ex where "ex = (\<lambda>p. multiplicity p fm)"
text \<open>The split of all prime factors into \<open>P1\<close> and \<open>P2\<close> only affects fields with prime characteristic.
For fields with characteristic $0$, \<open>P2\<close> is always empty.\<close>
definition P1 where "P1 = {f\<in>fac_set. \<not> p dvd ex f}"
definition P2 where "P2 = {f\<in>fac_set. p dvd ex f}"

text \<open>Assumptions on the degree of $f$ rewritten.\<close>
lemma deg_f_gr_0[simp]: "degree f > 0" using deg by auto
lemma f_nonzero[simp]: "f\<noteq>0" using deg degree_0 by blast
lemma fm_nonzero: "fm \<noteq> 0" using deg_f_gr_0  fm_def by auto


text \<open>Lemmas on \<open>fac_set\<close>, \<open>P1\<close> and \<open>P2\<close>. \<open>P1\<close> and \<open>P2\<close> are a partition of \<open>fac_set\<close>.\<close>
lemma fac_set_nonempty[simp]: "fac_set \<noteq> {}" unfolding fac_set_def
  by (metis deg_f_gr_0 degree_0 degree_1 degree_normalize fm_def 
      nat_less_le prod_mset.empty prod_mset_prime_factorization_weak 
      set_mset_eq_empty_iff)
lemma fac_set_P1_P2: "fac_set = P1 \<union> P2" 
  unfolding P1_def P2_def by auto

lemma P1_P2_intersect[simp]: "P1 \<inter> P2 = {}" 
  unfolding P1_def P2_def by auto

lemma finites[simp]: "finite fac_set" "finite P1" "finite P2" 
  unfolding P1_def P2_def fac_set_def by auto

text \<open>All elements of \<open>fac_set\<close> (and thus of \<open>P1\<close> and \<open>P2\<close>) are monic, irreducible, prime and 
prime elements.\<close>
lemma fac_set_prime[simp]: "prime x" if "x\<in>fac_set"
  using fac_set_def that by blast

lemma P1_prime[simp]: "prime x" if "x\<in>P1" 
  using P1_def fac_set_prime that by blast

lemma P2_prime[simp]: "prime x" if "x\<in>P2" 
  using P2_def fac_set_prime that by blast

lemma fac_set_monic[simp]: "monic x" if "x\<in>fac_set" 
  using fac_set_def that by (metis in_prime_factors_imp_prime 
      monic_normalize normalize_prime not_prime_0)
lemma P1_monic[simp]: "monic x" if "x\<in>P1"  
  using P1_def fac_set_monic that by blast
lemma P2_monic[simp]: "monic x" if "x\<in>P2"
  using P2_def fac_set_monic that by blast

lemma fac_set_prime_elem[simp]: "prime_elem x" if "x\<in>fac_set" 
  using fac_set_def that in_prime_factors_imp_prime by blast
lemma P1_prime_elem[simp]: "prime_elem x" if "x\<in>P1"
  using P1_def fac_set_prime that by blast
lemma P2_prime_elem[simp]: "prime_elem x" if "x\<in>P2"
  using P2_def fac_set_prime that by blast

lemma fac_set_irreducible[simp]: "irreducible x" if "x\<in>fac_set"
  using fac_set_def that fac_set_prime_elem by auto
lemma P1_irreducible[simp]: "irreducible x" if "x\<in>P1"
  using P1_def fac_set_prime that by blast
lemma P2_irreducible[simp]: "irreducible x" if "x\<in>P2" 
  using P2_def fac_set_prime that by blast


text \<open>All prime factors are nonzero. Also the derivative of a prime factor is nonzero.
The exponent of a prime factor is also nonzero.\<close>
lemma nonzero[simp]: "fj \<noteq> 0" if "fj\<in> fac_set"
  using fac_set_def that zero_not_in_prime_factors by blast

lemma nonzero_deriv[simp]: "pderiv fj \<noteq> 0" if "fj\<in> fac_set" 
  by (intro irreducible_imp_pderiv_nonzero)
    (use that fac_set_def in_prime_factors_imp_prime in \<open>auto\<close>)

lemma P1_ex_nonzero: "of_nat (ex x) \<noteq> (0:: 'e)" if "x\<in>P1" 
  using that P1_def p_def by (simp add: of_nat_eq_0_iff_char_dvd)

text \<open>A prime factor and its derivative are coprime. Also elements of \<open>P1\<close> and \<open>P2\<close> are coprime.\<close>
lemma deriv_coprime: "algebraic_semidom_class.coprime x (pderiv x)" 
  if "x\<in>fac_set" for x using irreducible_imp_separable that 
  using fac_set_def in_prime_factors_imp_prime by blast


lemma P1_P2_coprime: "algebraic_semidom_class.coprime x (\<Prod>f\<in>P2. f^ex f)" if "x\<in>P1"
  by (smt (verit) P1_def P2_def as_ufd.prime_elem_iff_irreducible fac_set_def 
      in_prime_factors_imp_prime irreducible_dvd_prod mem_Collect_eq 
      normalization_semidom_class.prime_def prime_dvd_power prime_imp_coprime primes_dvd_imp_eq that)

lemma P1_ex_P2_coprime: "algebraic_semidom_class.coprime (x^ex x) (\<Prod>f\<in>P2. f^ex f)" if "x\<in>P1"
  using P1_P2_coprime by (simp add: that)


text \<open>We now come to the interesting factorizations of the normalization of a polynomial.
It can be represented in Isabelle as the multi-set product \<open>prod_mset\<close> of the multi-set of its 
prime factors, or as a product of prime factors to the power of its multiplicity.
We can also split the product into two parts: The prime factors with exponent divisible by the 
cardinality of the finite field \<open>p\<close> (= the set \<open>P2\<close>) and those not divisible by \<open>p\<close> (= the set \<open>P1\<close>).\<close>
lemma f_fac: "fm = prod_mset fac"
  by (metis deg_f_gr_0 bot_nat_0.extremum_strict degree_0 fac_def fm_def in_prime_factors_iff 
      normalize_eq_0_iff normalize_prime normalized_prod_msetI prod_mset_prime_factorization_weak)

lemma fm_P1_P2: "fm = (\<Prod>fj\<in>P1. fj^(ex fj)) * (\<Prod>fj\<in>P2. fj^(ex fj))"
proof -
  have *: "fm = (\<Prod>fj\<in>fac_set. fj^(ex fj))" unfolding f_fac unfolding fac_def fac_set_def
    by (smt (verit, best) count_prime_factorization_prime ex_def in_prime_factors_imp_prime 
        prod.cong prod_mset_multiplicity)
  show ?thesis unfolding * using fac_set_P1_P2
      prod.union_disjoint[OF finites(2) finites(3) P1_P2_intersect] by auto
qed


text \<open>We now want to look at the derivative and its explicit form.
The problem for polynomials over fields with prime characteristic is that for prime factors with 
exponent divisible by the characteristic, the exponent as a field element equals $0$ and cancels out the 
respective term, i.e.: In a finite field $\mathbb{F}_{p^n}[x]$, if $f=g^p$ where $g$ is a prime 
polynomial and $p$ is the cardinality, then $f' = p\cdot g^{p-1} = 0$. 
This has nasty side effects in the elimination of repeated factors (ERF) algorithm.
As all summands with a derivative of a factor in \<open>P2\<close> cancel out, we can also write the derivative
as a sum over all derivatives over \<open>P1\<close> only.\<close>
definition deriv_part where
  "deriv_part = (\<lambda>y. Polynomial.smult (of_nat (ex y)) (pderiv y * y ^ (ex y - Suc 0) *
                (\<Prod>fj\<in>fac_set - {y}. fj ^ ex fj)))"

definition deriv_monic where 
  "deriv_monic = (\<lambda>y. pderiv y * y ^ (ex y - Suc 0) * (\<Prod>fj\<in>fac_set - {y}. fj ^ ex fj))"

lemma pderiv_fm: "pderiv fm = (\<Sum>f\<in>fac_set. deriv_part f)"
  unfolding deriv_part_def pderiv_exp_prod_monic[OF f_fac] Let_def fac_set_def fac_def ex_def 
    count_prime_factorization by (intro sum.cong, simp) 
    (smt (verit) DiffD1 One_nat_def in_prime_factors_iff mult_smult_left prod.cong)

lemma sumP2_deriv_zero: "(\<Sum>f\<in>P2. deriv_part f) = 0" 
  unfolding deriv_part_def unfolding P2_def  
  by (intro sum.neutral, use P2_def p_def of_nat_eq_0_iff_char_dvd in \<open>auto\<close>)

lemma pderiv_fm': "pderiv fm = (\<Sum>f\<in>P1. deriv_part f)" 
  by (subst pderiv_fm, subst fac_set_P1_P2, 
      subst sum.union_disjoint[OF finites(2) finites(3) P1_P2_intersect])
    (use sumP2_deriv_zero in \<open>auto\<close>)

definition deriv_P1 where
  "deriv_P1 = (\<lambda>y. Polynomial.smult (of_nat (ex y)) (pderiv y * y ^ (ex y - Suc 0) *
                (\<Prod>fj\<in>P1 - {y}. fj ^ ex fj)))"

lemma pderiv_fm'': "pderiv fm = (\<Prod>f\<in>P2. f^ex f) * (\<Sum>x\<in>P1. deriv_P1 x)"
proof (subst pderiv_fm', subst sum_distrib_left, intro sum.cong, safe, goal_cases)
  case (1 x)
  have *: "fac_set -{x} = P2 \<union> (P1-{x})" unfolding fac_set_P1_P2
    using 1 P1_P2_intersect by blast
  have **: "P2 \<inter> (P1 - {x}) = {}" using 1 P1_P2_intersect by blast
  have "(\<Prod>fj\<in>fac_set - {x}. fj ^ ex fj) = (\<Prod>f\<in>P2. f ^ ex f) * (\<Prod>fj\<in>P1 - {x}. fj ^ ex fj)"
    unfolding * by (intro prod.union_disjoint, auto simp add: **)
  then show ?case unfolding deriv_part_def deriv_P1_def by (auto simp add: algebra_simps)
qed 



text \<open>Some properties that $f_i^{e_i}$ for prime factors $f_i$ divides the summands of the 
derivative or not.\<close>

lemma ex_min_1_power_dvd_P1: "x ^ (ex x - 1) dvd deriv_part a" if "x\<in>P1" "a\<in>P1" for x a
proof (cases "x = a")
  case True
  then show ?thesis unfolding deriv_part_def 
    by (intro dvd_smult,subst dvd_mult2,subst dvd_mult) auto
next
  case False
  then have "x ^ (ex x - 1) dvd (\<Prod>fj\<in>fac_set - {a}. fj ^ ex fj)" 
    by (metis (no_types, lifting) Num.of_nat_simps(1) P1_def P1_ex_nonzero dvd_prod dvd_triv_right 
        finite_Diff finites(1) insertE insert_Diff mem_Collect_eq power_eq_if that(1) that(2))
  then show ?thesis unfolding deriv_part_def by (intro dvd_smult, subst dvd_mult) auto
qed

lemma ex_power_dvd_P2: "x ^ ex x dvd deriv_part a" if "x\<in>P2" "a\<in>P1" unfolding deriv_part_def
  by (intro dvd_smult, intro dvd_mult) (use P1_def P2_def that(1) that(2) in \<open>auto\<close>)


lemma ex_power_not_dvd: "\<not> y^ex y dvd deriv_monic y" if "y\<in>fac_set" 
proof 
  assume "y^ex y dvd deriv_monic y"
  then have "y * (y^(ex y-1)) dvd (pderiv y * (\<Prod>fj\<in>fac_set - {y}. fj ^ ex fj)) * (y^(ex y-1))"
    unfolding deriv_monic_def
    by (metis (no_types, lifting) count_prime_factorization_prime ex_def fac_set_def 
        in_prime_factors_imp_prime more_arith_simps(11) mult.commute not_in_iff numeral_nat(7) 
        power_eq_if that)
  then have *: "y dvd pderiv y * (\<Prod>fj\<in>fac_set - {y}. fj ^ ex fj)"
    unfolding dvd_mult_cancel_right dvd_smult_cancel by auto
  then have "y dvd (\<Prod>fj\<in>fac_set - {y}. fj ^ ex fj)" 
    using deriv_coprime[THEN coprime_dvd_mult_right_iff] \<open>y\<in>fac_set\<close> by auto
  then obtain fj where fj_def: "y dvd fj ^ ex fj" "fj\<in>fac_set - {y}" using prime_dvd_prod_iff
    by (metis (no_types, lifting) finites(1) \<open>y \<in> fac_set\<close> fac_set_def finite_Diff 
        in_prime_factors_iff)
  then have "y dvd fj" using prime_dvd_power
    by (metis fac_set_def in_prime_factors_imp_prime that)
  then have "coprime y fj" using fj_def(2)
    by (metis Diff_iff Diff_not_in fac_set_prime primes_dvd_imp_eq that)
  then show False by (metis \<open>y dvd fj\<close> coprimeE dvd_refl fac_set_def in_prime_factors_imp_prime 
        not_prime_unit that)
qed

lemma P1_ex_power_not_dvd: "\<not> y^ex y dvd deriv_part y" if "y\<in>P1" 
proof
  assume ass: "y^ex y dvd deriv_part y"
  have "y^ex y dvd deriv_monic y"
    using P1_ex_nonzero ass dvd_smult_iff that unfolding deriv_part_def deriv_monic_def by blast
  then show False using ex_power_not_dvd that unfolding P1_def by auto
qed

lemma P1_ex_power_not_dvd': "\<not> y^ex y dvd deriv_P1 y" if "y\<in>P1"
proof
  assume "y^ex y dvd deriv_P1 y" 
  then have ass: "y^ex y dvd pderiv y * y ^ (ex y - Suc 0) * (\<Prod>fj\<in>P1 - {y}. fj ^ ex fj)"
    using P1_ex_nonzero dvd_smult_iff that unfolding deriv_P1_def by blast
  then have "y * (y^(ex y-1)) dvd (pderiv y * (\<Prod>fj\<in>P1 - {y}. fj ^ ex fj)) * (y^(ex y-1))"
    by (metis (no_types, lifting) Num.of_nat_simps(1) P1_ex_nonzero more_arith_simps(11) 
        mult.commute numeral_nat(7) power_eq_if that)
  then have *: "y dvd pderiv y * (\<Prod>fj\<in>P1 - {y}. fj ^ ex fj)"
    unfolding dvd_mult_cancel_right dvd_smult_cancel by auto
  then have "y dvd (\<Prod>fj\<in>P1 - {y}. fj ^ ex fj)" 
    using deriv_coprime[THEN coprime_dvd_mult_right_iff] \<open>y\<in>P1\<close> fac_set_P1_P2 by blast
  then obtain fj where fj_def: "y dvd fj ^ ex fj" "fj\<in>P1 - {y}" using prime_dvd_prod_iff
    by (metis (no_types, lifting) P1_def finites(2) \<open>y \<in> P1\<close> fac_set_def finite_Diff 
        in_prime_factors_iff mem_Collect_eq)
  then have "y dvd fj" using prime_dvd_power
    by (metis UnCI fac_set_P1_P2 fac_set_def in_prime_factors_iff that)
  then show False
    by (metis DiffD1 Diff_not_in P1_prime fj_def(2) primes_dvd_imp_eq that) 
qed


text \<open>If the derivative of the normalized polynomial \<open>fm\<close> is zero, then all prime factors have
an exponent divisible by the cardinality \<open>p\<close>.\<close>
lemma pderiv0_p_dvd_count: "p dvd ex fj" if "fj\<in>fac_set" "pderiv fm = 0"
proof -
  have "(\<Sum>f\<in>fac_set. deriv_part f) = 0" using pderiv_fm \<open>pderiv fm = 0\<close> by auto
  then have zero: "Polynomial.smult (of_nat (ex fj)) (deriv_monic fj) + (\<Sum>f\<in>fac_set-{fj}. deriv_part f) = 0" 
    unfolding deriv_part_def deriv_monic_def
    by (metis (no_types, lifting) finites(1) sum.remove that(1))
  have dvd: "fj ^ ex fj dvd (\<Sum>f\<in>fac_set - {fj}. deriv_part f)" 
    unfolding deriv_part_def
    by (intro dvd_sum,intro dvd_smult,intro dvd_mult) 
      (use finites(1) that(1) in \<open>blast\<close>)
  have nondvd: "\<not> fj ^ ex fj dvd deriv_monic fj"
    using ex_power_not_dvd[OF \<open>fj\<in>fac_set\<close>] unfolding deriv_monic_def by auto
  have "of_nat (ex fj) = (0::'e)" by (rule one_summand_zero[OF zero dvd nondvd])
  then show ?thesis using p_def of_nat_eq_0_iff_char_dvd by blast
qed

text \<open>Properties on the multiplicity (i.e.\ the exponents) of prime factors in the factorization 
of the derivative.\<close>

lemma mult_fm[simp]: "count fac x = ex x" if "x\<in>fac_set"
  by (simp add: count_prime_factorization_prime ex_def fac_def that)

lemma mult_deriv1: "multiplicity x (pderiv fm) = ex x - 1"  
  if "x\<in>P1" "pderiv fm \<noteq> 0" for x
proof (subst multiplicity_eq_Max[OF that(2)])
  show "\<not> is_unit x" using that(1) using P1_def fac_set_def not_prime_unit by blast
  then have fin: "finite {n. x ^ n dvd pderiv fm}"
    using is_unit_iff_infinite_divisor_powers that(2) by blast 
  show "Max {n. x ^ n dvd pderiv fm} = ex x - 1" 
  proof (subst Max_eq_iff, goal_cases)
    case 2 then show ?case by (metis empty_Collect_eq one_dvd power_0)
  next
    case 3
    have dvd: "x ^(ex x-1) dvd pderiv fm" unfolding pderiv_fm' by(intro dvd_sum) 
        (use ex_min_1_power_dvd_P1[OF \<open>x\<in>P1\<close>] in \<open>auto\<close>)
    have not :"\<not> x^ex x dvd pderiv fm"
    proof 
      assume ass: "x ^ ex x dvd pderiv fm"
      have coprime: "algebraic_semidom_class.coprime (x^ex x) (\<Prod>f\<in>P2. f ^ ex f)" 
        using P1_ex_P2_coprime that(1) by auto
      then have "x ^ ex x dvd (\<Sum>y\<in>P1. deriv_P1 y)" 
        using ass coprime_dvd_mult_right_iff[OF coprime] unfolding pderiv_fm'' by auto
      also have "(\<Sum>y\<in>P1. deriv_P1 y) = deriv_P1 x + (\<Sum>y\<in>P1-{x}. deriv_P1 y)" 
        by (intro sum.remove, auto simp add: that)
      also have "\<dots> = deriv_P1 x + (x^ex x) * (\<Sum>y\<in>P1 - {x}. Polynomial.smult (of_nat (ex y))
      (pderiv y * y ^ (ex y - Suc 0) * (\<Prod>fj\<in>(P1 - {x})- {y}. fj ^ ex fj)))"
      proof -
        have *: "(pderiv xa * xa ^ (ex xa - Suc 0) * (\<Prod>fj\<in>P1 - {xa}. fj ^ ex fj)) =
          (x ^ ex x * (pderiv xa * xa ^ (ex xa - Suc 0) * (\<Prod>fj\<in>P1 - {x} - {xa}. fj ^ ex fj)))" 
          if "xa\<in>P1-{x}" for xa
        proof -
          have "x\<in>P1-{xa}" using that \<open>x\<in>P1\<close> by auto
          have fin: "finite (P1 - {xa})" by auto
          show ?thesis by (subst prod.remove[OF fin \<open>x\<in>P1-{xa}\<close>]) 
              (smt (verit, del_insts) Diff_insert2 Groups.mult_ac(3) insert_commute)
        qed
        show ?thesis unfolding deriv_P1_def by (auto simp add: sum_distrib_left *)
      qed
      finally have "x ^ ex x dvd deriv_P1 x + (x^ex x) * (\<Sum>y\<in>P1 - {x}. Polynomial.smult (of_nat (ex y))
      (pderiv y * y ^ (ex y - Suc 0) * (\<Prod>fj\<in>(P1 - {x})- {y}. fj ^ ex fj)))" by auto
      then have "x ^ ex x dvd deriv_P1 x" using dvd_add_times_triv_right_iff
        by (simp add: dvd_add_left_iff)
      then show False using P1_ex_power_not_dvd'[OF that(1)] by auto
    qed
    then have less: "a \<le> ex x - 1" if "a\<in>{n. x ^ n dvd pderiv fm}" for a 
      by (metis IntI Int_Collect Suc_pred' algebraic_semidom_class.unit_imp_dvd 
          bot_nat_0.not_eq_extremum is_unit_power_iff not_less_eq_eq power_le_dvd that)
    show ?case using dvd less by auto
  qed (use fin in \<open>auto\<close>)
qed


lemma mult_deriv: "multiplicity x (pderiv fm) \<ge> (if p dvd ex x then ex x else ex x - 1)"  
  if "x\<in>fac_set" "pderiv fm \<noteq> 0" 
proof (subst multiplicity_eq_Max[OF that(2)])
  show "\<not> is_unit x" using that(1) using fac_set_def not_prime_unit by blast
  then have fin: "finite {n. x ^ n dvd pderiv fm}"
    using is_unit_iff_infinite_divisor_powers that(2) by blast 
  show "Max {n. x ^ n dvd pderiv fm} \<ge> (if p dvd ex x then ex x else ex x - 1)"  
  proof (split if_splits, safe, goal_cases)
    case 1
    then have "x\<in>P2" unfolding P2_def using that by auto
    have dvd: "x ^ ex x dvd pderiv fm" unfolding pderiv_fm' by(intro dvd_sum)
        (use \<open>x \<in> P2\<close> ex_power_dvd_P2 in \<open>blast\<close>) 
    then show ?case by (intro Max_ge, auto simp add: fin)
  next
    case 2
    then have "x\<in>P1" unfolding P1_def using that by auto
    have dvd: "x ^(ex x-1) dvd pderiv fm" unfolding pderiv_fm' by(intro dvd_sum)
        (use \<open>x \<in> P1\<close> ex_min_1_power_dvd_P1 in \<open>blast\<close>)
    then show ?case by (intro Max_ge, auto simp add: fin)
  qed
qed

end
end