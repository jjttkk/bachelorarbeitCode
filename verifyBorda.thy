theory verifyBorda imports
"verifyVote"
begin
context elgamal_base
begin

(*The Preference_List is already encrypted,
 this function takes the encrypted Preference_List finds its elements in
 the Pair-List representing the Ballot where the votes are accumulated and 
 adds the "rank" of the element in the preference list
 (encrypted because of the homomorphic adding)*)
fun add_borda_ballot :: "'grp pub_key \<Rightarrow>'grp enclist \<Rightarrow> 'grp pair_list \<Rightarrow> 'grp pair_list"
    where
    "add_borda_ballot _ [] s = s"|
    "add_borda_ballot pk (x # xs) s = 
    (case find (\<lambda>(y,c). (x = y)) s of
      None \<Rightarrow> add_borda_ballot pk xs s | 
      Some (y, c) \<Rightarrow> let new_s = remove1 (y, c) s in
                 (y, add_pair(c::'grp cipher spmf) (aencrypt pk (get_grp_number(get_rank_num(x#xs) y)))) # add_borda_ballot pk xs new_s)"

(* Function to determine the result of the election using Borda voting *)
fun determine_election_result_borda :: "'grp priv_key \<Rightarrow> 'grp pub_key \<Rightarrow> 'grp Profile_List \<Rightarrow> 'grp declist" where
  "determine_election_result_borda sk pk profile_list = 
    filter_by_max 
      (find_max 
        (convert_to_num 
          (decrypt_2nds sk 
            (add_all_votes add_borda_ballot 
              (enc_profile_list pk profile_list) pk 
              (get_start_s pk (enc_list pk (hd profile_list)))))))
      (zip 
        (decrypt_1sts sk 
          (add_all_votes add_borda_ballot 
            (enc_profile_list pk profile_list) pk 
            (get_start_s pk (enc_list pk (hd profile_list))))) 
        (convert_to_num 
          (decrypt_2nds sk 
            (add_all_votes add_borda_ballot 
              (enc_profile_list pk profile_list) pk 
              (get_start_s pk (enc_list pk (hd profile_list)))))))"









lemma determine_election_result_borda_correct:
  assumes "valid_profile_list profile_list"
  shows "determine_election_result_borda sk pk profile_list = 
         filter_by_max 
      (find_max 
        (convert_to_num 
          (decrypt_2nds sk 
            (add_all_votes add_borda_ballot 
              (enc_profile_list pk profile_list) pk 
              (get_start_s pk (enc_list pk (hd profile_list)))))))
      (zip 
        (decrypt_1sts sk 
          (add_all_votes add_borda_ballot 
            (enc_profile_list pk profile_list) pk 
            (get_start_s pk (enc_list pk (hd profile_list))))) 
        (convert_to_num 
          (decrypt_2nds sk 
            (add_all_votes add_borda_ballot 
              (enc_profile_list pk profile_list) pk 
              (get_start_s pk (enc_list pk (hd profile_list)))))))"
  using assms
  by (simp add: determine_election_result_borda.simps)
end
end