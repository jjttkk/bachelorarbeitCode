theory verifyBorda imports
(*"verifyEncryptionDecryption"*)
"Game_Based_Crypto.Elgamal"
"verifiedVotingRuleConstruction/theories/Compositional_Structures/Basic_Modules/Component_Types/Social_Choice_Types/Refined_Types/Preference_List"
begin
context elgamal_base
begin

datatype ('a, 'b) tupel_list = Nil | Cons "('a \<times> 'b)" "('a, 'b) tupel_list"
(*
definition one :: "nat" where "one =  1"
definition zeros :: "nat list" where "zeros = replicate 0 (0::nat)"
definition plurality_values :: "nat list" where "plurality_values = one # zeros"
*)

(*nat list is list of preferences, [1,0,0,...] for Plurality-Voting
  Preference_List already encrypted*)(*
fun convert_preferencelist_to_ballot :: "'a Preference_List \<Rightarrow> nat list \<Rightarrow> ('a, 'b)  ballot"
  where
   "convert_preferencelist_to_ballot [] _ = Nil" |
   "convert_preferencelist_to_ballot (x # xs) (y # ys) = Cons(x, aencrypt (y)) (convert_preferencelist_to_ballot xs ys) "
*)
(*first ballot is new ballot to add,
 second ballot is Sum-Ballot which holds final result at the end*)(*
fun add_ballots :: "('a, 'b) ballot \<Rightarrow>('a, 'b) ballot \<Rightarrow>('a, 'b) ballot "
  where
  "add_ballots [] sum_ballot = sum_ballot"|
  "add_ballots ((option_sum, value_b) # options) sum_ballot = 
  (case find (\<lambda>(option_sum, value_sum). option_b = option_sum) sum_ballot of
    None \<Rightarrow> add_ballots options sum_ballot |
    Some (option_sum, value_sum) \<Rightarrow> (option_sum,value_sum + value_b) # add ballots options sum_ballot"
      *)

(*The Preference_List is already encrypted, this function takes the encrypted Preference_List
 finds the top-preference/first element of the Preference-List in the tupel_list representing 
 the Ballot where the votes are accumulated and adds 1 
 (encrypted 1 because of the homomorphic adding)*)
fun add_plurality_ballot :: "'a Preference_List \<Rightarrow> ('a, 'b) tupel_list \<Rightarrow> ('a, 'b) tupel_list"
    where
    "add_plurality_ballot (sum_list::('a,'b) tupel_list) = sum_list"|
    "add_plurality_ballot (x # xs) (sum_list::('a,'b) tupel_list) = 
    (case find (\<lambda>(y,_). x = y) sum_list of
      None \<Rightarrow> add_plurality_ballot xs(sum_list::('a,'b) tupel_list) | 
      Some (y, count) \<Rightarrow> Cons (y,count + aencrypt(pk, 1)) # remove1 (\<lambda>(a,_).a = y) sum_list)"
end
end