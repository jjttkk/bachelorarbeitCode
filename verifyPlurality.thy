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


(* Function to determine the result of the election using Plurality voting *)
fun determine_election_result_plurality :: "'grp priv_key \<Rightarrow> 'grp pub_key \<Rightarrow> 'grp Profile_List \<Rightarrow> 'grp option list" where
  "determine_election_result_plurality sk pk profile_list = 
    filter_by_max 
      (find_max 
        (convert_to_numbers 
          (extract_and_decrypt_seconds sk 
            (add_all_votes add_plurality_ballot 
              (encrypt_profile_list pk profile_list) pk 
              (get_start_s pk (enc_list pk (hd profile_list)))))))
      (zip 
        (extract_and_decrypt_firsts sk 
          (add_all_votes add_plurality_ballot 
            (encrypt_profile_list pk profile_list) pk 
            (get_start_s pk (enc_list pk (hd profile_list))))) 
        (convert_to_numbers 
          (extract_and_decrypt_seconds sk 
            (add_all_votes add_plurality_ballot 
              (encrypt_profile_list pk profile_list) pk 
              (get_start_s pk (enc_list pk (hd profile_list)))))))"

end
end