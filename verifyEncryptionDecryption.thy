theory verifyEncryptionDecryption imports
"Game_Based_Crypto.Elgamal"
begin

context elgamal_base
begin

(*Functions to parse the type for proving the lemmas*)
definition fix_type:: "'grp list \<Rightarrow> 'grp option spmf list"
  where "fix_type xs = map (\<lambda>x. return_spmf (Some x)) xs" 

definition fix_type_single:: "'grp \<Rightarrow> 'grp option spmf"
  where "fix_type_single x = return_spmf (Some x)"

(* Function to encrypt a list of group elements using the given public key *)
fun enc_list :: "'grp pub_key \<Rightarrow> 'grp list \<Rightarrow> ('grp cipher spmf) list" 
  where
   "enc_list pk [] = []" |
   "enc_list pk (x # xs) = (aencrypt pk x) # enc_list pk xs"

(* Function to decrypt a list of encrypted group elements using the given private key
   Returns a list of optional group elements, where None represents a failed decryption *)  
fun dec_list :: "'grp priv_key \<Rightarrow> ('grp cipher spmf) list \<Rightarrow> 'grp option list"
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