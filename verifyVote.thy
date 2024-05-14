theory verifyVote imports
"Game_Based_Crypto.Elgamal"
"verifiedVotingRuleConstruction/theories/Compositional_Structures/Basic_Modules/Component_Types/Social_Choice_Types/Refined_Types/Preference_List"
begin
context elgamal_base
begin

(*function to add the second part (encrypted number) of types 'grp cipher spmf
 used in verifyPlurality and verifyBorda*)
definition add_pair :: "('grp \<times> 'grp) spmf \<Rightarrow> ('grp \<times> 'grp) spmf \<Rightarrow> ('grp \<times> 'grp) spmf" where
"add_pair x_spmf y_spmf = do {
    (x1, x2) \<leftarrow> x_spmf;
    (y1, y2) \<leftarrow> y_spmf;
    return_spmf (x1, x2 \<otimes> y2)
}"

(*function to create the initial (all options get count 1(encrypted), because 0 does not work)
Pair-List representing the Ballot where the votes are accumulated*)
fun get_start_s :: "'grp pub_key \<Rightarrow> 'grp cipher spmf list  \<Rightarrow> ('grp cipher spmf \<times> 'grp cipher spmf) list" where
"get_start_s pk [] = []"|
"get_start_s pk (x # xs) = (x, (aencrypt pk (one \<G>))) # get_start_s pk xs"

(*function which takes the result pair-list of the vote from add_all_votes_plurality or 
 add_all_votes_borda and calculates the maximum amount of votes an option got
 therefore it has to create a new list consisting of the second parts of the pairs of the first list
 decrypt this list with dec_list and transfer the type to num
 then the Max function from Isabelle Main can find the maximum*)
fun get_max:: "('grp cipher spmf \<times> 'grp cipher spmf) list \<Rightarrow> nat" 
  where
    "get_max [] _ = 0" |
    "get_max s sk = (
    let 
        second_parts = map snd s;
        decrypted_values = dec_list sk second_parts; 
        num_values = map_spmf (\<lambda>x. case x of None \<Rightarrow> 0 | Some v \<Rightarrow> nat_of_grp v) decrypted_values;
    in Max (set_spmf num_values)
)"

(*function which takes the result pair-list of the vote from add_all_votes_plurality or 
 add_all_votes_borda and makes a list of the first parts of the pairs to decrypt with dec_list, 
 and makes a list of the second parts of the pairs to decrypt with dec_list. the lists are then 
 put back together as a pair list like before. then get_max is used to find the maximum of the 
 original input list and filters the new list: only the elements where the second part equals
 the maximum are put in another list *)
fun get_winners::  "('grp cipher spmf \<times> 'grp cipher spmf) list \<Rightarrow> 'grp list" 
  where
"get_winners [] _ = []" |
"get_winners s sk = (
    let 
        first_parts = map fst s; 
        second_parts = map snd s;
        decrypted_firsts = dec_list sk first_parts;
        decrypted_seconds = dec_list sk second_parts;
        decrypted_pairs = zip decrypted_firsts decrypted_seconds;
        max_vote = Max (set_spmf (map_spmf (\<lambda>x. case x of None \<Rightarrow> 0 | Some v \<Rightarrow> nat_of_grp v) decrypted_seconds));
        winners = filter (\<lambda>(_, c). case c of None \<Rightarrow> False | Some v \<Rightarrow> nat_of_grp v = max_vote) decrypted_pairs
    in map (\<lambda>(f, _). case f of None \<Rightarrow> dummy_grp | Some v \<Rightarrow> v) winners
)"


end
end