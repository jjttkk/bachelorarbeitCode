theory verifyVote imports
Main
"Game_Based_Crypto.Elgamal"
"verifyEncryptionDecryption"
"verifiedVotingRuleConstruction/theories/Compositional_Structures/Basic_Modules/Component_Types/Social_Choice_Types/Refined_Types/Preference_List"
"verifiedVotingRuleConstruction/theories/Compositional_Structures/Basic_Modules/Component_Types/Social_Choice_Types/Refined_Types/Profile_List"
begin
context elgamal_base
begin

(* Function to homomorphically add the second part (encrypted number) of types 'grp cipher spmf*)
definition add_pair :: "('grp \<times> 'grp) spmf \<Rightarrow> ('grp \<times> 'grp) spmf \<Rightarrow> ('grp \<times> 'grp) spmf" where
"add_pair x y = do {
    (x1, x2) \<leftarrow> x;
    (y1, y2) \<leftarrow> y;
    return_spmf (x1, x2 \<otimes> y2)
}"

(* Function to add all preference lists in a profile list to the ballot
   using either add_borda_ballot or add_plurality_ballot *)
fun add_all_votes :: "('grp pub_key \<Rightarrow> 'grp cipher spmf Preference_List \<Rightarrow> ('grp cipher spmf \<times> 'grp cipher spmf) list \<Rightarrow> ('grp cipher spmf \<times> 'grp cipher spmf) list) \<Rightarrow> 'grp cipher spmf Profile_List \<Rightarrow> 'grp pub_key \<Rightarrow> ('grp cipher spmf \<times> 'grp cipher spmf) list \<Rightarrow> ('grp cipher spmf \<times> 'grp cipher spmf) list" 
  where
"add_all_votes add_ballot [] pk s = s" |
"add_all_votes add_ballot (p # ps) pk s = 
    (let 
        updated_s = add_ballot pk p s
    in add_all_votes add_ballot ps pk updated_s)"

(* Function to convert a group element to a natural number *)
function get_nat_from_grp::"'grp \<Rightarrow> nat" where
"get_nat_from_grp g = (if g = one \<G> then 0 else Suc (get_nat_from_grp (g \<otimes> inv (one \<G>))))"
  by pat_completeness auto

(* Function to get the rank of an encrypted group element in an encrypted preference list
   Returns the number of elements in the list minus the rank of the element *)
fun get_number ::  "'grp cipher spmf Preference_List \<Rightarrow> 'grp cipher spmf \<Rightarrow> nat" 
  where
  "get_number [] _ = 0"|
  "get_number xs y = length xs - rank_l xs y"

(* Function to convert a natural number to a group element *)
fun get_grp_number::"nat \<Rightarrow> 'grp" where
"get_grp_number 0 = (one \<G>)"|
"get_grp_number (Suc n) = (one \<G>) \<otimes> (get_grp_number n)"

(*function to create the initial (all options get count 1(encrypted)
Pair-List representing the Ballot where the votes are accumulated*)
fun get_start_s :: "'grp pub_key \<Rightarrow> 'grp cipher spmf list  \<Rightarrow> ('grp cipher spmf \<times> 'grp cipher spmf) list" where
"get_start_s pk [] = []"|
"get_start_s pk (x # xs) = (x, (aencrypt pk (one \<G>))) # get_start_s pk xs"

(* Function to encrypt a profile list *)
fun encrypt_profile_list :: "'grp pub_key \<Rightarrow> 'grp Profile_List \<Rightarrow> ('grp cipher spmf Preference_List) list" where
  "encrypt_profile_list pk [] = []" |
  "encrypt_profile_list pk (p # ps) = (enc_list pk p) # encrypt_profile_list pk ps"

(* Function to extract and decrypt the first elements of a list of pairs *)
fun extract_and_decrypt_firsts :: "'grp priv_key \<Rightarrow> ('grp cipher spmf \<times> 'grp cipher spmf) list \<Rightarrow> 'grp option list" where
  "extract_and_decrypt_firsts sk [] = []" |
  "extract_and_decrypt_firsts sk ((c, _) # xs) = 
    (case (map_option (\<lambda>y. adecrypt sk y) (the_elem c)) of
      None \<Rightarrow> None # extract_and_decrypt_firsts sk xs |
      Some None \<Rightarrow> None # extract_and_decrypt_firsts sk xs |
      Some (Some msg) \<Rightarrow> Some msg # extract_and_decrypt_firsts sk xs)"

(* Function to extract and decrypt the second elements of a list of pairs *)
fun extract_and_decrypt_seconds :: "'grp priv_key \<Rightarrow> ('grp cipher spmf \<times> 'grp cipher spmf) list \<Rightarrow> 'grp option list" where
  "extract_and_decrypt_seconds sk [] = []" |
  "extract_and_decrypt_seconds sk ((_, c) # xs) = 
    (case (map_option (\<lambda>y. adecrypt sk y) (the_elem c)) of
      None \<Rightarrow> None # extract_and_decrypt_seconds sk xs |
      Some None \<Rightarrow> None # extract_and_decrypt_seconds sk xs |
      Some (Some msg) \<Rightarrow> Some msg # extract_and_decrypt_seconds sk xs)"

(* Function to convert a list of optional group elements to a list of natural numbers
   using get_nat_from_grp, with None elements converted to 0 *)
fun convert_to_numbers :: "'grp option list \<Rightarrow> nat list" where
  "convert_to_numbers [] = []" |
  "convert_to_numbers (None # xs) = 0 # convert_to_numbers xs" |
  "convert_to_numbers (Some g # xs) = get_nat_from_grp g # convert_to_numbers xs"

(* Function to find the maximum value in a list of natural numbers *)
definition find_max :: "nat list \<Rightarrow> nat" where
  "find_max ns = Max (set ns)"

(* Function to create a new list of pairs from decrypted lists *)
fun create_decrypted_pairs :: "'grp option list \<Rightarrow> 'grp option list \<Rightarrow> ('grp option \<times> 'grp option) list" where
  "create_decrypted_pairs [] [] = []" |
  "create_decrypted_pairs (x # xs) [] = []" |
  "create_decrypted_pairs [] (y # ys) = []"|
  "create_decrypted_pairs (x # xs) (y # ys) = (x, y) # create_decrypted_pairs xs ys"

(* Function to filter a list of pairs by a maximum value, keeping only pairs with the maximum value as the second element *)
fun filter_by_max :: "nat \<Rightarrow> ('grp option \<times> nat) list \<Rightarrow> 'grp option list" where
  "filter_by_max _ [] = []" |
  "filter_by_max max_val ((x, n) # xs) = 
    (if n = max_val then x # filter_by_max max_val xs else filter_by_max max_val xs)"

end
end