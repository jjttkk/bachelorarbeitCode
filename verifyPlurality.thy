theory verifyPlurality imports
"verifyVote"
begin
context elgamal_base
begin 

(*The Preference_List is already encrypted,
 this function takes the encrypted Preference_List finds its first element in
 the Pair-List representing the Ballot where the votes are accumulated and adds 1 
 (encrypted 1 because of the homomorphic adding)*)
fun add_plurality_ballot :: "'grp pub_key \<Rightarrow>'grp enc_pref_list \<Rightarrow> 'grp pair_list \<Rightarrow> 'grp pair_list"
    where
    "add_plurality_ballot _ [] s = s"|
    "add_plurality_ballot pk (x # xs) s = 
    (case find (\<lambda>(y,c). (x = y)) s of
      None \<Rightarrow> add_plurality_ballot pk xs s | 
      Some (y, c) \<Rightarrow> let new_s = remove1 (y, c) s in
                 (y, add_pair(c::'grp cipher spmf) (aencrypt pk (one \<G>))) # new_s)"


(* Function to determine the result of the election using Plurality voting *)
fun determine_election_result_plurality :: "'grp priv_key \<Rightarrow> 'grp pub_key \<Rightarrow> 'grp Profile_List \<Rightarrow> 'grp declist" where
  "determine_election_result_plurality sk pk profile_list = 
    filter_by_max 
      (find_max 
        (convert_to_num 
          (decrypt_2nds sk 
            (add_all_votes add_plurality_ballot 
              (enc_profile_list pk profile_list) pk 
              (get_start_s pk (enc_list pk (hd profile_list)))))))
      (zip 
        (decrypt_1sts sk 
          (add_all_votes add_plurality_ballot 
            (enc_profile_list pk profile_list) pk 
            (get_start_s pk (enc_list pk (hd profile_list))))) 
        (convert_to_num 
          (decrypt_2nds sk 
            (add_all_votes add_plurality_ballot 
              (enc_profile_list pk profile_list) pk 
              (get_start_s pk (enc_list pk (hd profile_list)))))))"

end
end