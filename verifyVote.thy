theory verifyVote imports
"Game_Based_Crypto.Elgamal"
"verifiedVotingRuleConstruction/theories/Compositional_Structures/Basic_Modules/Component_Types/Social_Choice_Types/Refined_Types/Preference_List"
begin
context elgamal_base
begin

(*function to add the second part (encrypted number) of types 'grp cipher spmf
 used in verifyPlurality and verifyBorda*)
definition add_pair :: "('grp \<times> 'grp) spmf \<Rightarrow> ('grp \<times> 'grp) spmf \<Rightarrow> ('grp \<times> 'grp) spmf" where
"add_pair x_spmf y_spmf = do {
    (x1, x2) \<leftarrow> x_spmf;
    (y1, y2) \<leftarrow> y_spmf;
    return_spmf (x1, x2 \<otimes> y2)
}"

(*function to create the initial (all options get count 1(encrypted), because 0 does not work)
Pair-List representing the Ballot where the votes are accumulated*)
fun get_start_s :: "'grp pub_key \<Rightarrow> 'grp cipher spmf list  \<Rightarrow> ('grp cipher spmf \<times> 'grp cipher spmf) list" where
"get_start_s pk [] = []"|
"get_start_s pk (x # xs) = (x, (aencrypt pk (one \<G>))) # get_start_s pk xs"








end
end