theory verifyBorda imports
"verifyVote"
"verifyEncryptionDecryption"
"Game_Based_Crypto.Elgamal"
"verifiedVotingRuleConstruction/theories/Compositional_Structures/Basic_Modules/Component_Types/Social_Choice_Types/Refined_Types/Preference_List"
"verifiedVotingRuleConstruction/theories/Compositional_Structures/Basic_Modules/Component_Types/Social_Choice_Types/Refined_Types/Profile_List"
begin
context elgamal_base
begin

(*The Preference_List is already encrypted,
 this function takes the encrypted Preference_List finds its elements in
 the Pair-List representing the Ballot where the votes are accumulated and 
 adds the "rank" of the element in the preference list
 (encrypted because of the homomorphic adding)*)
fun add_borda_ballot :: "'grp pub_key \<Rightarrow>'grp cipher spmf Preference_List \<Rightarrow> ('grp cipher spmf \<times> 'grp cipher spmf) list \<Rightarrow> ('grp cipher spmf \<times> 'grp cipher spmf) list"
    where
    "add_borda_ballot _ [] s = s"|
    "add_borda_ballot pk (x # xs) s = 
    (case find (\<lambda>(y,c). (x = y)) s of
      None \<Rightarrow> add_borda_ballot pk xs s | 
      Some (y, c) \<Rightarrow> let new_s = remove1 (y, c) s in
                 (y, add_pair(c::'grp cipher spmf) (aencrypt pk (get_grp_number(get_number(x#xs) y)))) # add_borda_ballot pk xs new_s)"

(* Function to determine the result of the election using Borda voting *)
fun determine_election_result_borda :: "'grp priv_key \<Rightarrow> 'grp pub_key \<Rightarrow> 'grp Profile_List \<Rightarrow> 'grp option list" where
  "determine_election_result_borda sk pk profile_list = 
    filter_by_max 
      (find_max 
        (convert_to_numbers 
          (extract_and_decrypt_seconds sk 
            (add_all_votes add_borda_ballot 
              (encrypt_profile_list pk profile_list) pk 
              (get_start_s pk (enc_list pk (hd profile_list)))))))
      (zip 
        (extract_and_decrypt_firsts sk 
          (add_all_votes add_borda_ballot 
            (encrypt_profile_list pk profile_list) pk 
            (get_start_s pk (enc_list pk (hd profile_list))))) 
        (convert_to_numbers 
          (extract_and_decrypt_seconds sk 
            (add_all_votes add_borda_ballot 
              (encrypt_profile_list pk profile_list) pk 
              (get_start_s pk (enc_list pk (hd profile_list)))))))"

end
end