theory verifyPlurality imports
(*"verifyEncryptionDecryption"*)
"Game_Based_Crypto.Elgamal"
"verifiedVotingRuleConstruction/theories/Compositional_Structures/Basic_Modules/Component_Types/Social_Choice_Types/Refined_Types/Preference_List"
begin
context elgamal_base
begin 

fun get_start_s :: "'grp pub_key \<Rightarrow> 'grp cipher spmf list  \<Rightarrow> ('grp cipher spmf \<times> 'grp cipher spmf) list" where
"get_start_s pk [] = []"|
"get_start_s pk (x # xs) = (x, (aencrypt pk (one \<G>))) # get_start_s pk xs"

definition add_pair :: "('grp \<times> 'grp) spmf \<Rightarrow> ('grp \<times> 'grp) spmf \<Rightarrow> ('grp \<times> 'grp) spmf" where
"add_pair x_spmf y_spmf = do {
    (x1, x2) \<leftarrow> x_spmf;
    (y1, y2) \<leftarrow> y_spmf;
    return_spmf (x1, x2 \<otimes> y2)
}"


(*The Preference_List is already encrypted,
 this function takes the encrypted Preference_List finds its first element in
 the Pair-List representing the Ballot where the votes are accumulated and adds 1 
 (encrypted 1 because of the homomorphic adding)*)
fun add_plurality_ballot :: "'grp pub_key \<Rightarrow>'grp cipher spmf Preference_List \<Rightarrow> ('grp cipher spmf \<times> 'grp cipher spmf) list \<Rightarrow> ('grp cipher spmf \<times> 'grp cipher spmf) list"
    where
    "add_plurality_ballot _ [] s = s"|
    "add_plurality_ballot pk (x # xs) s = 
    (case find (\<lambda>(y,c). (x = y)) s of
      None \<Rightarrow> add_plurality_ballot pk xs s | 
      Some (y, c) \<Rightarrow> let new_s = remove1 (y, c) s in
                 (y, add_pair(c::'grp cipher spmf) (aencrypt pk (one \<G>))) # new_s)"
end
end