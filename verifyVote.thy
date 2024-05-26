theory verifyVote imports
Main
"Game_Based_Crypto.Elgamal"
"verifyEncryptionDecryption"
"verifiedVotingRuleConstruction/theories/Compositional_Structures/Basic_Modules/Component_Types/Social_Choice_Types/Refined_Types/Preference_List"
begin
context elgamal_base
begin

(*function to add the second part (encrypted number) of types 'grp cipher spmf
 used in verifyPlurality and verifyBorda*)
definition add_pair :: "('grp \<times> 'grp) spmf \<Rightarrow> ('grp \<times> 'grp) spmf \<Rightarrow> ('grp \<times> 'grp) spmf" where
"add_pair x y = do {
    (x1, x2) \<leftarrow> x;
    (y1, y2) \<leftarrow> y;
    return_spmf (x1, x2 \<otimes> y2)
}"

(*function to create the initial (all options get count 1(encrypted), because 0 does not work)
Pair-List representing the Ballot where the votes are accumulated*)
fun get_start_s :: "'grp pub_key \<Rightarrow> 'grp cipher spmf list  \<Rightarrow> ('grp cipher spmf \<times> 'grp cipher spmf) list" where
"get_start_s pk [] = []"|
"get_start_s pk (x # xs) = (x, (aencrypt pk (one \<G>))) # get_start_s pk xs"


function get_number_from_grp::"'grp \<Rightarrow> nat" where
"get_number_from_grp g = (if g = one \<G> then 0 else Suc (get_number_from_grp (g \<otimes> inv (one \<G>))))"
  by pat_completeness auto


(*function which takes the result pair-list of the vote from add_all_votes_plurality or 
 add_all_votes_borda and calculates the maximum amount of votes an option got,
 therefore it has to create a new list consisting of the second parts of the pairs of the first list
 decrypt this list with dec_list and transfer the type to num
 then the Max function from Isabelle Main can find the maximum
fun get_max :: "('grp cipher spmf \<times> 'grp cipher spmf) list \<Rightarrow> 'grp priv_key \<Rightarrow> nat" where
"get_max [] _ = 0" |
"get_max s sk = (
        second_parts = map snd s;
        decrypted_values = map (\<lambda>c. map_spmf (adecrypt sk) c) second_parts;
       
)"

(*function which takes the result pair-list of the vote from add_all_votes_plurality or 
 add_all_votes_borda and makes a list of the first parts of the pairs to decrypt with dec_list, 
 and makes a list of the second parts of the pairs to decrypt with dec_list. the lists are then 
 put back together as a pair list like before. then get_max is used to find the maximum of the 
 original input list and filters the new list: only the elements where the second part equals
 the maximum are put in another list *)
fun get_winners :: "('grp cipher spmf \<times> 'grp cipher spmf) list \<Rightarrow> 'grp priv_key \<Rightarrow> 'grp list" where
"get_winners [] _ = []" |
"get_winners s sk = (
    let 
        first_parts = map fst s;
        second_parts = map snd s;
        decrypted_firsts = map (\<lambda>c. map_spmf (adecrypt sk) c) first_parts;
        decrypted_seconds = map (\<lambda>c. map_spmf (adecrypt sk) c) second_parts;
        decrypted_pairs = zip ...
        max_vote = get_max s sk;
        winners = filter ... decrypted_pairs
    in map (\<lambda>(f, _). f) winners
)"*)

end
end