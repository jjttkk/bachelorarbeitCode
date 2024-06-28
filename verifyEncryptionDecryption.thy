theory verifyEncryptionDecryption imports
"HOL-Library.List_Lexorder"
"HOL-Probability.Probability"
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
type_synonym 'grp pair = "('grp cipher) spmf"
type_synonym 'grp opt_spmf = "'grp option spmf"
type_synonym 'grp add_ballot_function = "('grp pub_key \<Rightarrow> 'grp enc_pref_list \<Rightarrow> 'grp pair_list \<Rightarrow> 'grp pair_list)"
type_synonym 'grp dec_pair_list = "('grp option \<times> 'grp option) list"

context elgamal_base
begin

(* Function to encrypt a list of group elements using the given public key *)
fun enc_list :: "'grp pub_key \<Rightarrow> 'grp list \<Rightarrow> 'grp enclist" 
  where
   "enc_list pk [] = []" |
   "enc_list pk (x # xs) = (aencrypt pk x) # enc_list pk xs"

(* Function to decrypt a list of encrypted group elements using the given private key
   Returns a list of optional group elements, where None represents a failed decryption   *)
fun dec_list :: "'grp priv_key \<Rightarrow> 'grp enclist \<Rightarrow> 'grp declist"
  where 
    "dec_list sk [] = []" |
    "dec_list sk (x # xs) = (case (map_option (\<lambda>y. adecrypt sk y) (the_elem x)) of
                                None \<Rightarrow> None # dec_list sk xs |
                                Some None \<Rightarrow> None # dec_list sk xs |
                                Some (Some msg) \<Rightarrow> Some msg # dec_list sk xs)"

(*
_____________________________________________________________________________________________
LEMMAS
_____________________________________________________________________________________________
*)
lemma enc_list_correct:
  "enc_list pk xs = map (aencrypt pk) xs"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by simp
qed

lemma dec_list_correct:
  "dec_list sk (x # xs) = 
    (case map_option (\<lambda>y. adecrypt sk y) (the_elem x) of
      None \<Rightarrow> None # dec_list sk xs
    | Some None \<Rightarrow> None # dec_list sk xs
    | Some (Some msg) \<Rightarrow> Some msg # dec_list sk xs)"
  using  dec_list.simps(2) HOL.nitpick_simp(1053)
  by presburger

lemma dec_list_empty:
  "dec_list sk [] = []"
  by auto

lemma dec_list_none:
  fixes sk :: "'grp priv_key"
  and xs :: "'grp list"
  and x :: "'grp"
  and enc_xs :: "'grp enclist"
  and enc_x ::"'grp cipher spmf"
  assumes "enc_xs = enc_list (pub_key sk) xs "
  shows "dec_list sk (enc_x # enc_xs) = None # dec_list sk enc_xs"
  using assms dec_list_correct
proof-
  have "enc_list (pub_key sk) xs = map (aencrypt (pub_key sk)) xs"
    by (simp add: enc_list_correct)
  moreover have "dec_list sk (enc_x # enc_xs) = 
    (case map_option (\<lambda>y. adecrypt sk y) (the_elem enc_x) of
      None \<Rightarrow> None # dec_list sk enc_xs
    | Some None \<Rightarrow> None # dec_list sk enc_xs
    | Some (Some msg) \<Rightarrow> Some msg # dec_list sk enc_xs)"
    by (simp add: dec_list_correct)
  ultimately show ?thesis
    using assms 
    apply (simp add: dec_list.simps)
    by (cases "map_option (\<lambda>y. adecrypt sk y) (the_elem enc_x)") auto
qed 

lemma dec_list_some_none:
  fixes sk :: "'grp priv_key"
  and xs :: "'grp list"
  and x :: "'grp"
  and enc_xs :: "'grp enclist"
  and enc_x ::"'grp cipher spmf"
assumes "enc_xs = enc_list (pub_key sk) xs"
and  "map_option (\<lambda>y. adecrypt sk y) (the_elem enc_x) = Some None"
  shows "dec_list sk (enc_x # enc_xs) = None # dec_list sk enc_xs"
  using assms dec_list_none 
  by blast

lemma dec_list_some_some:
  fixes sk :: "'grp priv_key"
  and xs :: "'grp list"
  and x :: "'grp"
  and enc_xs :: "'grp enclist"
  and enc_x ::"'grp cipher spmf"
  assumes "enc_xs = enc_list (pub_key sk) xs "
  shows "dec_list sk (enc_x # enc_xs) = Some msg # dec_list sk enc_xs"
and "map_option (\<lambda>y. adecrypt sk y) (the_elem enc_x) = Some (Some msg)"
  using assms dec_list_none enc_list_correct dec_list_some_none dec_list_correct
  proof -
  have "enc_list (pub_key sk) xs = map (aencrypt (pub_key sk)) xs"
    by (simp add: enc_list_correct)
  moreover have "dec_list sk (enc_x # enc_xs) = 
    (case map_option (\<lambda>y. adecrypt sk y) (the_elem enc_x) of
      None \<Rightarrow> None # dec_list sk enc_xs
    | Some None \<Rightarrow> None # dec_list sk enc_xs
    | Some (Some m) \<Rightarrow> Some m # dec_list sk enc_xs)"
    by (simp add: dec_list_correct)
  
qed


end

end