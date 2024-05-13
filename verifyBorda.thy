theory verifyBorda imports
"Game_Based_Crypto.Elgamal"
"verifiedVotingRuleConstruction/theories/Compositional_Structures/Basic_Modules/Component_Types/Social_Choice_Types/Refined_Types/Preference_List"
begin
context elgamal_base
begin

(*function to create the initial (all options get count 1(encrypted), because 0 does not work)
Pair-List representing the Ballot where the votes are accumulated*)
fun get_start_s :: "'grp pub_key \<Rightarrow> 'grp cipher spmf list  \<Rightarrow> ('grp cipher spmf \<times> 'grp cipher spmf) list" where
"get_start_s pk [] = []"|
"get_start_s pk (x # xs) = (x, (aencrypt pk (one \<G>))) # get_start_s pk xs"

(*function to add the second part (encrypted number) of types 'grp cipher spmf*)
definition add_pair :: "('grp \<times> 'grp) spmf \<Rightarrow> ('grp \<times> 'grp) spmf \<Rightarrow> ('grp \<times> 'grp) spmf" where
"add_pair x_spmf y_spmf = do {
    (x1, x2) \<leftarrow> x_spmf;
    (y1, y2) \<leftarrow> y_spmf;
    return_spmf (x1, x2 \<otimes> y2)
}"

(*function to get the number to encrypt and add to the count as nat*)
fun getNumber ::  "'grp cipher spmf Preference_List \<Rightarrow> 'grp cipher spmf \<Rightarrow> nat" 
  where
  "getNumber [] _ = 0"|
  "getNumber xs y = length xs - rank_l xs y"

(*function to get the number from getNumber as 'grp*)
fun get_grp_number::"nat \<Rightarrow> 'grp" where
"get_grp_number 0 = (one \<G>)"|
"get_grp_number (Suc n) = (one \<G>) \<otimes> (get_grp_number n)"

(*The Preference_List is already encrypted,
 this function takes the encrypted Preference_List finds its first element in
 the Pair-List representing the Ballot where the votes are accumulated and adds 1 
 (encrypted 1 because of the homomorphic adding)*)
fun add_borda_ballot :: "'grp pub_key \<Rightarrow>'grp cipher spmf Preference_List \<Rightarrow> ('grp cipher spmf \<times> 'grp cipher spmf) list \<Rightarrow> ('grp cipher spmf \<times> 'grp cipher spmf) list"
    where
    "add_borda_ballot _ [] s = s"|
    "add_borda_ballot pk (x # xs) s = 
    (case find (\<lambda>(y,c). (x = y)) s of
      None \<Rightarrow> add_borda_ballot pk xs s | 
      Some (y, c) \<Rightarrow> let new_s = remove1 (y, c) s in
                 (y, add_pair(c::'grp cipher spmf) (aencrypt pk (get_grp_number(getNumber(x#xs) y)))) # add_borda_ballot pk xs new_s)"
end
end