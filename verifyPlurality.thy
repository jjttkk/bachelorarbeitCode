theory verifyPlurality imports
(*"verifyEncryptionDecryption"*)
"Game_Based_Crypto.Elgamal"
"verifiedVotingRuleConstruction/theories/Compositional_Structures/Basic_Modules/Component_Types/Social_Choice_Types/Refined_Types/Preference_List"
begin
context elgamal_base
begin

datatype ('a, 'b) tupel_list = Nil | Cons "('a \<times> 'b)" "('a, 'b) tupel_list"

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

(*The Preference_List is already encrypted, 
 this function takes the encrypted Preference_List finds its first element in
 the tupel_list representing the Ballot where the votes are accumulated and adds 1 
 (encrypted 1 because of the homomorphic adding)*)
fun add_plurality_ballot :: "'grp pub_key \<Rightarrow>'a Preference_List \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list"
    where
    "add_plurality_ballot _ [] (s) = s"|
    "add_plurality_ballot pk (x # xs) (s) = 
    (case find (\<lambda>(y,c). (x = y)) s of
      None \<Rightarrow> add_plurality_ballot pk xs (s) | 
      Some (y, c) \<Rightarrow> (y,c + (aencrypt pk 1)) # remove1 (\<lambda>(a,_).a = y) s)"
end
end