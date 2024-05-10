theory verifyPlurality imports
"verifyEncryptionDecryption"
"Game_Based_Crypto.Elgamal"
"verifiedVotingRuleConstruction/theories/Compositional_Structures/Basic_Modules/Component_Types/Social_Choice_Types/Refined_Types/Preference_List"
begin

datatype ('a, 'b) ballot = Nil | Cons "('a \<times> 'b)" "('a, 'b) ballot"

definition one :: "nat" where "one =  1"
definition zeros :: "nat list" where "zeros = replicate 0 (0::nat)"
definition plurality_values :: "nat list" where "plurality_values = one # zeros"


(*nat list is list of preferences, [1,0,0,...] for Plurality-Voting
  Preference_List already encrypted*)
fun convert_preferencelist_to_ballot :: "'a Preference_List \<Rightarrow> nat list \<Rightarrow> ('a, 'b)  ballot"
  where
   "convert_preferencelist_to_ballot [] _ = Nil" |
   "convert_preferencelist_to_ballot (x # xs) (y # ys) = Cons(x, aencrypt (y)) (convert_preferencelist_to_ballot xs ys) "

(*first ballot is new ballot to add,
 second ballot is Sum-Ballot which holds final result at the end*)
fun add_ballots :: "ballot \<Rightarrow> ballot \<Rightarrow> ballot "
  where
  "add_ballots [] sum_ballot = sum_ballot"|
  "add_ballots ((option_sum, value_b) # options) sum_ballot = 
  (case find (\<lambda>(option_sum, value_sum). option_b = option_sum) sum_ballot of
    None \<Rightarrow> add_ballots options sum_ballot |
    Some (option_sum, value_sum) \<Rightarrow> (option_sum,value_sum + value_b) # add ballots options sum ballot "
    


end