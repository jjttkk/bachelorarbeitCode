theory verifyVote imports
"verifyEncryptionDecryption"
begin
context elgamal_base
begin
(*
____________________________________________________
FUNCTIONS TO ADD THINGS TOGETHER
____________________________________________________
*)

(* Function to homomorphically add the second part (encrypted number) of types 'grp cipher spmf*)
definition add_pair :: "'grp pair \<Rightarrow> 'grp pair \<Rightarrow> 'grp pair" where
"add_pair x y = do {
    (x1, x2) \<leftarrow> x;
    (y1, y2) \<leftarrow> y;
    return_spmf (x1, x2 \<otimes> y2)
}"

(* Function to add all preference lists in a profile list to the ballot
   using either add_borda_ballot or add_plurality_ballot *)
fun add_all_votes :: "'grp add_ballot_function \<Rightarrow> 'grp enc_prof_list \<Rightarrow> 'grp pub_key \<Rightarrow> 'grp pair_list \<Rightarrow> 'grp pair_list" 
  where
"add_all_votes add_ballot [] pk s = s" |
"add_all_votes add_ballot (p # ps) pk s = 
    (let 
        updated_s = add_ballot pk p s
    in add_all_votes add_ballot ps pk updated_s)"

(*
____________________________________________________
FUNCTIONS TO CONVERT TYPES
____________________________________________________
*)

(* Function to convert a group element to a natural number *)
function get_nat_from_grp::"'grp \<Rightarrow> nat" where
"get_nat_from_grp g = (if g = one \<G> then 0 else Suc (get_nat_from_grp (g \<otimes> inv (one \<G>))))"
  by pat_completeness auto

(* Function to get the rank of an encrypted group element in an encrypted preference list
   Returns the number of elements in the list minus the rank of the element *)
fun get_rank_num ::  "'grp enc_pref_list \<Rightarrow> 'grp cipher spmf \<Rightarrow> nat" 
  where
  "get_rank_num [] _ = 0"|
  "get_rank_num xs y = length xs - rank_l xs y"

(* Function to convert a natural number to a group element *)
fun get_grp_number::"nat \<Rightarrow> 'grp" where
"get_grp_number 0 = (one \<G>)"|
"get_grp_number (Suc n) = (one \<G>) \<otimes> (get_grp_number n)"

(* Function to convert a list of optional group elements to a list of natural numbers
   using get_nat_from_grp, with None elements converted to 0 *)
fun convert_to_num :: "'grp declist \<Rightarrow> nat list" where
  "convert_to_num [] = []" |
  "convert_to_num (None # xs) = 0 # convert_to_num xs" |
  "convert_to_num (Some g # xs) = get_nat_from_grp g # convert_to_num xs"

(*
____________________________________________________
FUNCTIONS TO ENCRYPT/DECRYPT
____________________________________________________
*)

(* Function to encrypt a profile list *)
fun enc_profile_list :: "'grp pub_key \<Rightarrow> 'grp Profile_List \<Rightarrow> ('grp enc_pref_list) list" where
  "enc_profile_list pk [] = []" |
  "enc_profile_list pk (p # ps) = (enc_list pk p) # enc_profile_list pk ps"

(* Function to extract and decrypt the first elements of a list of pairs *)
fun decrypt_1sts :: "'grp priv_key \<Rightarrow> 'grp pair_list \<Rightarrow> 'grp declist" where
  "decrypt_1sts sk [] = []" |
  "decrypt_1sts sk ((c, _) # xs) = 
    (case (map_option (\<lambda>y. adecrypt sk y) (the_elem c)) of
      None \<Rightarrow> None # decrypt_1sts sk xs |
      Some None \<Rightarrow> None # decrypt_1sts sk xs |
      Some (Some msg) \<Rightarrow> Some msg # decrypt_1sts sk xs)"

(* Function to extract and decrypt the second elements of a list of pairs *)
fun decrypt_2nds :: "'grp priv_key \<Rightarrow> 'grp pair_list \<Rightarrow> 'grp declist" where
  "decrypt_2nds sk [] = []" |
  "decrypt_2nds sk ((_, c) # xs) = 
    (case (map_option (\<lambda>y. adecrypt sk y) (the_elem c)) of
      None \<Rightarrow> None # decrypt_2nds sk xs |
      Some None \<Rightarrow> None # decrypt_2nds sk xs |
      Some (Some msg) \<Rightarrow> Some msg # decrypt_2nds sk xs)"

(*
____________________________________________________
FUNCTIONS TO GET THE VOTES WITH MAXIMUM 
NUMBER OF VOTES
____________________________________________________
*)

(* Function to find the maximum value in a list of natural numbers *)
definition find_max :: "nat list \<Rightarrow> nat" where
  "find_max ns = Max (set ns)"

(* Function to filter a list of pairs by a maximum value, keeping only pairs with the maximum 
   value as the second element *)
fun filter_by_max :: "nat \<Rightarrow> ('grp option \<times> nat) list \<Rightarrow> 'grp declist" where
  "filter_by_max _ [] = []" |
  "filter_by_max max_val ((x, n) # xs) = 
    (if n = max_val then x # filter_by_max max_val xs else filter_by_max max_val xs)"

(*
____________________________________________________
OTHER HELPERS
____________________________________________________
*)

(*function to create the initial (all options get count 1(encrypted)
Pair-List representing the Ballot where the votes are accumulated*)
fun get_start_s :: "'grp pub_key \<Rightarrow> 'grp cipher spmf list  \<Rightarrow> 'grp pair_list" where
"get_start_s pk [] = []"|
"get_start_s pk (x # xs) = (x, (aencrypt pk (one \<G>))) # get_start_s pk xs"

(* Function to create a new list of pairs from decrypted lists *)
fun create_dec_pairs :: "'grp declist \<Rightarrow> 'grp declist \<Rightarrow> 'grp dec_pair_list" where
  "create_dec_pairs [] [] = []" |
  "create_dec_pairs (x # xs) [] = []" |
  "create_dec_pairs [] (y # ys) = []"|
  "create_dec_pairs (x # xs) (y # ys) = (x, y) # create_dec_pairs xs ys"




(*______________________________________________________________________________________________
LEMMAS
________________________________________________________________________________________________*)

lemma find_max_correct:
  assumes "xs \<noteq> []"
  shows "find_max xs = Max (set xs)"
  using assms
  by (simp add: find_max_def)

(*
lemma filter_by_max_correct:
  assumes "max_val = find_max (map snd xs)"
  shows "filter_by_max max_val xs = map fst (filter (\<lambda>(x, n). n = max_val) xs)"
  using assms enc_list_correct 
  apply (simp add: filter_by_max.simps)
  sorry
 *)


lemma enc_profile_list_correct:
  "enc_profile_list pk ps = map (enc_list pk) ps"
  by (induction ps, auto)

lemma add_all_votes_correct:
  "add_all_votes add_ballot ps pk s = foldl (\<lambda>acc p. add_ballot pk p acc) s ps"
  by (induction ps arbitrary: s, auto)

lemma get_start_s_correct:
  "get_start_s pk xs = map (\<lambda>x. (x, aencrypt pk (one \<G>))) xs"
  by (induction xs, auto)

lemma add_pair_correct:
  "add_pair x y = do {
    (x1, x2) \<leftarrow> x;
    (y1, y2) \<leftarrow> y;
    return_spmf (x1, x2 \<otimes> y2)
  }"
  unfolding add_pair_def by simp

lemma get_rank_num_correct:
  "get_rank_num xs y = length xs - rank_l xs y"
  by (induction xs) auto

lemma convert_to_num_correct:
  "convert_to_num xs = map (\<lambda>x. case x of None \<Rightarrow> 0 | Some g \<Rightarrow> get_nat_from_grp g) xs"
  by (induction xs) auto

lemma decrypt_1sts_correct:
  "decrypt_1sts sk xs = map (\<lambda>(c, _). case (map_option (\<lambda>y. adecrypt sk y) (the_elem c)) of
    None \<Rightarrow> None | Some None \<Rightarrow> None | Some (Some msg) \<Rightarrow> Some msg) xs"
  by (induction xs) auto

lemma decrypt_2nds_correct:
  "decrypt_2nds sk xs = map (\<lambda>(_, c). case (map_option (\<lambda>y. adecrypt sk y) (the_elem c)) of
    None \<Rightarrow> None | Some None \<Rightarrow> None | Some (Some msg) \<Rightarrow> Some msg) xs"
  by (induction xs) auto

lemma create_dec_pairs_correct:
  "create_dec_pairs xs ys = zip xs ys"
  by (induction xs ys rule: create_dec_pairs.induct) auto



end
end