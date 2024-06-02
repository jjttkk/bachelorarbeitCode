theory verifyEncryptionDecryption imports
"Game_Based_Crypto.Elgamal"
"verifiedVotingRuleConstruction/theories/Compositional_Structures/Basic_Modules/Component_Types/Social_Choice_Types/Refined_Types/Preference_List"
"verifiedVotingRuleConstruction/theories/Compositional_Structures/Basic_Modules/Component_Types/Social_Choice_Types/Refined_Types/Profile_List"

begin
type_synonym 'grp' pub_key = "'grp'"
type_synonym 'grp' cipher = "'grp' \<times> 'grp'"
type_synonym 'grp enc_pref_list = "'grp cipher spmf Preference_List"
type_synonym 'grp enc_prof_list = "'grp cipher spmf Profile_List"
type_synonym 'grp enclist = "('grp cipher spmf) list"
type_synonym 'grp declist = "'grp option list"
type_synonym 'grp pair_list = "('grp cipher spmf \<times> 'grp cipher spmf) list"
type_synonym 'grp pair = "('grp \<times> 'grp) spmf"
type_synonym 'grp opt_spmf = "'grp option spmf"
type_synonym 'grp add_ballot_function = "('grp pub_key \<Rightarrow> 'grp enc_pref_list \<Rightarrow> 'grp pair_list \<Rightarrow> 'grp pair_list)"
type_synonym 'grp dec_pair_list = "('grp option \<times> 'grp option) list"

context elgamal_base
begin

(*Functions to parse the type for proving the lemmas*)
definition fix_type:: "'grp list \<Rightarrow> 'grp opt_spmf list"
  where "fix_type xs = map (\<lambda>x. return_spmf (Some x)) xs" 

definition fix_type_single:: "'grp \<Rightarrow> 'grp opt_spmf"
  where "fix_type_single x = return_spmf (Some x)"

(* Function to encrypt a list of group elements using the given public key *)
fun enc_list :: "'grp pub_key \<Rightarrow> 'grp list \<Rightarrow> 'grp enclist" 
  where
   "enc_list pk [] = []" |
   "enc_list pk (x # xs) = (aencrypt pk x) # enc_list pk xs"

(* Function to decrypt a list of encrypted group elements using the given private key
   Returns a list of optional group elements, where None represents a failed decryption *)  
fun dec_list :: "'grp priv_key \<Rightarrow> 'grp enclist \<Rightarrow> 'grp declist"
  where 
    "dec_list sk [] = []" |
    "dec_list sk (x # xs) = (case (map_option (\<lambda>y. adecrypt sk y) (the_elem x)) of
                                None \<Rightarrow> None # dec_list sk xs |
                                Some None \<Rightarrow> None # dec_list sk xs |
                                Some (Some msg) \<Rightarrow> Some msg # dec_list sk xs)"

lemma enc_list_correct:
  "enc_list pk xs = map (aencrypt pk) xs"
proof (induction xs)
  case Nil
  then show ?case by simp
  case (Cons x xs)
  then show ?case by simp
qed

lemma dec_list_correct:
  "dec_list sk (map (aencrypt pk) xs) = map (adecrypt sk) (map (aencrypt pk) xs)"



end

end