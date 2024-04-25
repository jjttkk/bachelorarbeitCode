section \<open>Boolos Curious Proof Problem\<close>

theory Boolos_Curious_Inference_Automated imports Main
begin   (* sledgehammer_params[timeout=60] *)

text\<open>First declare a non-empty type @{term "i"} of objects (natural numbers in the context of this paper).\<close>
typedecl i


text \<open>The signature for BCP consists of four uninterpreted constant symbols.\<close>
consts
 e :: "i" ("\<^bold>e")  \<comment>\<open>one\<close>
 s :: "i\<Rightarrow>i" ("\<^bold>s_")  \<comment>\<open>successor function\<close>
 f :: "i\<Rightarrow>i\<Rightarrow>i" ("\<^bold>f__")  \<comment>\<open>binary function; axiomatised below as Ackermann function\<close>
 d :: "i\<Rightarrow>bool" ("\<^bold>d_")  \<comment>\<open>arbitrary uninterpreted unary predicate\<close>


text \<open>Axioms @{term "A1"}-@{term "A3"} model the Ackermann function and Axioms @{term "A4"} and @{term "A5"}
stipulate the properties of predicate @{term "d"}.\<close>
axiomatization where
A1: "\<forall>n. \<^bold>fn\<^bold>e = \<^bold>s\<^bold>e"  and   \<comment>\<open>Axiom 1 for Ackermann function @{term "f"}\<close>
A2: "\<forall>y. \<^bold>f\<^bold>e\<^bold>sy = \<^bold>s\<^bold>s\<^bold>f\<^bold>ey"  and   \<comment>\<open>Axiom 2 for Ackermann function @{term "f"}\<close>
A3: "\<forall>x y. \<^bold>f\<^bold>sx\<^bold>sy = \<^bold>fx\<^bold>f(\<^bold>sx)y"  and  \<comment>\<open>Axiom 3 for Ackermann function @{term "f"}\<close>
A4: "\<^bold>d\<^bold>e"  and  \<comment>\<open>@{term "d"} (an arbitrary predicate) holds for one\<close>
A5: "\<forall>x. \<^bold>dx \<longrightarrow> \<^bold>d\<^bold>sx"  \<comment>\<open>if @{term "d"} holds for @{term "x"} it also holds for the successor of @{term "x"}\<close>

text \<open>Trying to prove automatically with \textit{Sledgehammer} @{cite Sledgehammer} that @{term "d"} holds
for fssssesssse still fails at this point. As Boolos'
explains, a naive first-order proof would require more modus ponens steps (with A5 and A4) than
there are atoms in the
universe.\<close>
lemma "\<^bold>d\<^bold>f\<^bold>s\<^bold>s\<^bold>s\<^bold>s\<^bold>e\<^bold>s\<^bold>s\<^bold>s\<^bold>s\<^bold>e" \<comment>\<open>sledgehammer\<close> oops  \<comment>\<open>no proof found; timeout\<close>

section \<open>Automated Proof: Using Two Definitions\<close>

text \<open>We interactively provide two shorthand notations @{term "ind"} and @{term "p"}. After their
introduction a proof can be found fully automatically with \textit{Sledgehammer}. @{term "ind X"}
is defined to hold if
and only if  @{term "X"} is `inductive' over  @{term "e"} and  @{term "s"}.
 @{term "pxy"} holds if and only if @{term "pxy"} is in smallest inductive set
over  @{term "e"} and  @{term "s"}.
Note that the symbols @{term "ind"} and @{term "p"} do not occur in the BCP problem
statement.\<close>
definition ind ("\<^bold>i\<^bold>n\<^bold>d_") where "ind \<equiv> \<lambda>X. X\<^bold>e \<and> (\<forall>x. X x \<longrightarrow> X \<^bold>sx)"
definition p ("\<^bold>p_") where "p \<equiv> \<lambda>x y. (\<lambda>z::i. (\<forall>X. \<^bold>i\<^bold>n\<^bold>d X \<longrightarrow> X z)) \<^bold>f x y"

text \<open>Using these definitions, state-of-art higher-order ATPs integrated with Isabelle/HOL can now fully
automatically prove Boolos' Curious Problem:\<close>
theorem "\<^bold>d\<^bold>f\<^bold>s\<^bold>s\<^bold>s\<^bold>s\<^bold>e\<^bold>s\<^bold>s\<^bold>s\<^bold>s\<^bold>e"  \<comment>\<open>@{term sledgehammer}\<close> (*
   sledgehammer [z3]  (* z3 found a proof... *)
   sledgehammer [vampire]  (* vampire found a proof... *)
   sledgehammer [remote_leo2]  (* remote_leo2 found a proof... *)
   sledgehammer [e] (* e found a proof ... *)
   sledgehammer [zipperposition]  (* zipperposition found a proof... *)
   sledgehammer [cvc4]  (* No proof found *)
   sledgehammer [verit] (* No proof found *)
   sledgehammer [spass] (* No proof found *)
   sledgehammer [remote_leo3]  (* No proof found *)  *)
 by (metis A1 A2 A3 A4 A5 ind_def p_def)  \<comment>\<open>metis proof reconstruction succeeds\<close>

text \<open>In experiments (using a MacBook Pro (16-inch, 2019), 2,6 GHz 6-Core Intel Core i7,
16 GB 2667 MHz DDR4) running Isabelle2022 automatically found proofs were reported by various theorem
provers, including
@{term "Z3"} @{cite Z3},
@{term "Vampire"} @{cite Vampire},
@{term "Zipperposition"} @{cite Zipperpin},
@{term "E"} @{cite Eprover},
and Leo-II (@{term "remote_leo2"}) @{cite Leo2}.\<close>

section \<open>Automated Proof: Using a Single Definition\<close>

definition p' ("\<^bold>p'_") where
  "p' \<equiv> \<lambda>x y. (\<lambda>z::i. (\<forall>X. (X\<^bold>e \<and> (\<forall>x. X x \<longrightarrow> X \<^bold>sx)) \<longrightarrow> X z)) \<^bold>f x y"

theorem "\<^bold>d\<^bold>f\<^bold>s\<^bold>s\<^bold>s\<^bold>s\<^bold>e\<^bold>s\<^bold>s\<^bold>s\<^bold>s\<^bold>e"  \<comment>\<open>@{term "sledgehammer (A1 A2 A3 A4 A5 p'_def)"}\<close>  (*
  sledgehammer[remote_leo2]  (A1 A2 A3 A4 A5 p'_def)
 \<comment>\<open>sledgehammer [z3] (A1 A2 A3 A4 A5 p'\_def)   (* z3 found a proof... *)
   sledgehammer [vampire] (A1 A2 A3 A4 A5 p'\_def)  (* vampire found a proof... *)
   sledgehammer [remote\_leo2] (A1 A2 A3 A4 A5 p'\_def)  (* remote\_leo2 found a proof... *)
   sledgehammer [zipperposition] (A1 A2 A3 A4 A5 p'\_def)  (* zipperposition found a proof... *)
   sledgehammer [e] (A1 A2 A3 A4 A5 p'\_def)  (* e found a proof ... *)
   sledgehammer [cvc4] (A1 A2 A3 A4 A5 p'\_def)  (* No proof found *)
   sledgehammer [verit] (A1 A2 A3 A4 A5 p'\_def)  (* No proof found *)
   sledgehammer [spass] (A1 A2 A3 A4 A5 p'\_def)  (* No proof found *)
   sledgehammer [remote\_leo3] (A1 A2 A3 A4 A5 p'\_def)  (* No proof found *)\<close> *)
  by (smt A1 A2 A3 A4 A5 p'_def)  \<comment>\<open>smt proof reconstruction succeeds\<close>

text \<open>In experiments (using the same environment as above) several provers reported
proofs, including @{term "Z3"} and @{term "E"}.\<close>


section\<open>Proof Reconstruction: E's Proof from @{cite BCI}\<close>
text \<open>In this section we reconstruct and verify in Isabelle/HOL the proof argument found by E
as reported in @{cite BCI}. Analysing E's proof we can identify the following five lemmata:\<close>
lemma L1a: "\<^bold>i\<^bold>n\<^bold>d d" by (simp add: A4 A5 ind_def)
lemma L1b: "\<forall>x. \<^bold>px\<^bold>e" by (simp add: A1 ind_def p_def)
lemma L1c: "\<^bold>i\<^bold>n\<^bold>d \<^bold>p\<^bold>e" by (metis A2 L1b ind_def p_def)
lemma L2: "\<forall>x Y. (\<^bold>i\<^bold>n\<^bold>d \<^bold>px \<and> \<^bold>i\<^bold>n\<^bold>d \<^bold>p\<^bold>sx \<and> \<^bold>i\<^bold>n\<^bold>d Y) \<longrightarrow> Y\<^bold>f\<^bold>sx\<^bold>s\<^bold>s\<^bold>s\<^bold>s\<^bold>e" by (metis ind_def p_def)
lemma L3: "\<forall>x. \<^bold>i\<^bold>n\<^bold>d \<^bold>px \<longrightarrow> \<^bold>i\<^bold>n\<^bold>d \<^bold>p\<^bold>sx" by (metis A3 L1b ind_def p_def)


text \<open>Using these lemmata E then constructs the following refutation argument:\<close>
theorem "\<^bold>d\<^bold>f\<^bold>s\<^bold>s\<^bold>s\<^bold>s\<^bold>e\<^bold>s\<^bold>s\<^bold>s\<^bold>s\<^bold>e"
  proof -
    { assume L4: "\<not>\<^bold>d\<^bold>f\<^bold>s\<^bold>s\<^bold>s\<^bold>s\<^bold>e\<^bold>s\<^bold>s\<^bold>s\<^bold>s\<^bold>e"
      have L5: "\<not>\<^bold>i\<^bold>n\<^bold>d \<^bold>p\<^bold>s\<^bold>s\<^bold>s\<^bold>s\<^bold>e \<or> \<not>\<^bold>i\<^bold>n\<^bold>d \<^bold>p\<^bold>s\<^bold>s\<^bold>s\<^bold>e" using L1a L1b L1c L2 L4 by blast
      have L6: "\<not>\<^bold>i\<^bold>n\<^bold>d \<^bold>p\<^bold>s\<^bold>s\<^bold>s\<^bold>e \<and> \<not>\<^bold>i\<^bold>n\<^bold>d \<^bold>p\<^bold>s\<^bold>s\<^bold>e \<and> \<not>\<^bold>i\<^bold>n\<^bold>d \<^bold>p\<^bold>s\<^bold>e" using L3 L5 by blast
      have "False" using L1c L3 L6 by auto
    }
  then show ?thesis by blast
  qed

text \<open>This refutation argument can alternatively be replaced by:\<close>
theorem "\<^bold>d\<^bold>f\<^bold>s\<^bold>s\<^bold>s\<^bold>s\<^bold>e\<^bold>s\<^bold>s\<^bold>s\<^bold>s\<^bold>e"
  proof -
    have L7: "\<^bold>i\<^bold>n\<^bold>d \<^bold>p\<^bold>s\<^bold>e" using L1c L3 by blast
    have L8: "\<^bold>i\<^bold>n\<^bold>d \<^bold>p\<^bold>s\<^bold>s\<^bold>e" using L3 L7 by blast
    have L9: "\<^bold>i\<^bold>n\<^bold>d \<^bold>p\<^bold>s\<^bold>s\<^bold>s\<^bold>e" using L3 L8 by blast
    have L10: "\<^bold>i\<^bold>n\<^bold>d \<^bold>p\<^bold>s\<^bold>s\<^bold>s\<^bold>s\<^bold>e" using L3 L9 by blast
    have L11: "(\<^bold>i\<^bold>n\<^bold>d \<^bold>p\<^bold>s\<^bold>s\<^bold>s\<^bold>e \<and> \<^bold>i\<^bold>n\<^bold>d \<^bold>p\<^bold>s\<^bold>s\<^bold>s\<^bold>s\<^bold>e \<and> \<^bold>i\<^bold>n\<^bold>d d)" using L10 L1a L9 by blast
  then show ?thesis using L2 by blast
qed


text \<open>Lemma @{term "L2"} can actually be simplified (this was also hinted at by an anonymous
reviewer of @{cite J63}):\<close>
lemma L2_1: "\<forall>x Y. (\<^bold>i\<^bold>n\<^bold>d \<^bold>px \<and> \<^bold>i\<^bold>n\<^bold>d Y) \<longrightarrow> Y\<^bold>fx\<^bold>e" by (metis ind_def p_def)
lemma L2_2: "\<forall>x Y. (\<^bold>i\<^bold>n\<^bold>d \<^bold>px \<and> \<^bold>i\<^bold>n\<^bold>d Y) \<longrightarrow> Y\<^bold>fx\<^bold>s\<^bold>e" by (metis ind_def p_def)
lemma L2_3: "\<forall>x Y. (\<^bold>i\<^bold>n\<^bold>d \<^bold>px \<and> \<^bold>i\<^bold>n\<^bold>d Y) \<longrightarrow> Y\<^bold>fx\<^bold>s\<^bold>s\<^bold>e" by (metis ind_def p_def)
lemma L2_4: "\<forall>x Y. (\<^bold>i\<^bold>n\<^bold>d \<^bold>px \<and> \<^bold>i\<^bold>n\<^bold>d Y) \<longrightarrow> Y\<^bold>fx\<^bold>s\<^bold>s\<^bold>s\<^bold>e" by (metis ind_def p_def)
lemma L2_5: "\<forall>x Y. (\<^bold>i\<^bold>n\<^bold>d \<^bold>px \<and> \<^bold>i\<^bold>n\<^bold>d Y) \<longrightarrow> Y\<^bold>fx\<^bold>s\<^bold>s\<^bold>s\<^bold>s\<^bold>e" by (metis ind_def p_def)
text \<open>etc.\<close>

text \<open>The following statement, however, has a countermodel.\<close>
lemma L2_1: "\<forall>x y Y. (\<^bold>i\<^bold>n\<^bold>d \<^bold>px \<and> \<^bold>i\<^bold>n\<^bold>d Y) \<longrightarrow> Y\<^bold>f x y"
  nitpick[user_axioms,expect=genuine] oops \<comment>\<open>countermodel by nitpick\<close>


  text \<open>Instead of using @{term "L2"} we can now use @{term "L2_5"} in our proof of BCP from above:\<close>

theorem "\<^bold>d\<^bold>f\<^bold>s\<^bold>s\<^bold>s\<^bold>s\<^bold>e\<^bold>s\<^bold>s\<^bold>s\<^bold>s\<^bold>e"
  proof -
    have L7: "\<^bold>i\<^bold>n\<^bold>d \<^bold>p\<^bold>s\<^bold>e" using L1c L3 by blast
    have L8: "\<^bold>i\<^bold>n\<^bold>d \<^bold>p\<^bold>s\<^bold>s\<^bold>e" using L3 L7 by blast
    have L9: "\<^bold>i\<^bold>n\<^bold>d \<^bold>p\<^bold>s\<^bold>s\<^bold>s\<^bold>e" using L3 L8 by blast
    have L10: "\<^bold>i\<^bold>n\<^bold>d \<^bold>p\<^bold>s\<^bold>s\<^bold>s\<^bold>s\<^bold>e" using L3 L9 by blast
    have L11: "(\<^bold>i\<^bold>n\<^bold>d \<^bold>p\<^bold>s\<^bold>s\<^bold>s\<^bold>e \<and> \<^bold>i\<^bold>n\<^bold>d \<^bold>p\<^bold>s\<^bold>s\<^bold>s\<^bold>s\<^bold>e \<and> \<^bold>i\<^bold>n\<^bold>d d)" using L10 L1a L9 by blast
  then show ?thesis using L2_5 by blast
qed



section\<open>Conclusion\<close>
text \<open>Isabelle/HOL data sources were provided in relation to @{cite J63}, which describes recent progress
and remaining challenges in automating Boolos' Curious Problem.
The interactive introduction of lemmas, as still exercised in @{cite KetlandAFP} and earlier
in @{cite BoolosOmegaMizar}, is no longer necessary, since higher-order theorem provers are
now able to speculate the required lemmas automatically, provided that appropriate shorthand
notations are provided (see the definitions of @{term "ind"} and @{term "p"}).

Since Boolos' example for speeding up proofs is interesting in several respects, it is now being used as
an exercise in lecture courses at several universities (including University of Bamberg, University
of Greifswald, University of Luxembourg, Free University of Berlin); having our source files
permanently maintained in AFP hence makes sense.\<close>

end




