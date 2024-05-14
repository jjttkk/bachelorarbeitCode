theory verifyPlurality imports
"verifyVote"
"verifyEncryptionDecryption"
"Game_Based_Crypto.Elgamal"
"verifiedVotingRuleConstruction/theories/Compositional_Structures/Basic_Modules/Component_Types/Social_Choice_Types/Refined_Types/Preference_List"
"verifiedVotingRuleConstruction/theories/Compositional_Structures/Basic_Modules/Component_Types/Social_Choice_Types/Refined_Types/Profile_List"
begin
context elgamal_base
begin 

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

(*this function applys the function "add_plurality_ballot" on each element of the
 profile list (which is a list of preference lists, but encrypt that element before mit enc_list.
 the first element of "add_plurality_ballot" is a public key "pk", the second is the current 
 preference list and the third is for the first round "get_start_s" called with pk and the first
 preference list, after that it is always the output of the "add_plurality_ballot"-call before*)
fun add_all_votes_plurality :: "'grp Profile_List \<Rightarrow> 'grp pub_key => ('grp cipher spmf \<times> 'grp cipher spmf) list \<Rightarrow> ('grp cipher spmf \<times> 'grp cipher spmf) list" 
  where
"add_all_votes_plurality [] pk s = s" |
"add_all_votes_plurality (p # ps) pk s = 
    (let 
        encrypted_p = enc_list pk p;
        updated_s = add_plurality_ballot pk encrypted_p s
    in add_all_votes_plurality ps pk updated_s)"


end
end