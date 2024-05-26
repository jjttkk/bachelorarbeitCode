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

fun enc_list :: "'grp pub_key \<Rightarrow> 'grp list \<Rightarrow> ('grp cipher spmf) list" 
  where
   "enc_list pk [] = []" |
   "enc_list pk (x # xs) = (aencrypt pk x) # enc_list pk xs"



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
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xsmap_option
  then show ?case
    by (simp add: dec_list.simps adecrypt_def split: option.splits)
qed


(* Function to encrypt a list of elements using Elgamal-Encryption from Game Based Crypto 
fun enc_list :: "'grp pub_key \<Rightarrow> 'grp list \<Rightarrow> 'grp cipher list spmf"
  where
    "enc_list _ [] = return_spmf []" |
    "enc_list pub_key (x # xs) = do {
      enc_x \<leftarrow> aencrypt pub_key x;
      enc_xs \<leftarrow> enc_list pub_key xs;
      return_spmf (enc_x # enc_xs)
    }"

(* Function to decrypt a list of elements using Elgamal-Decryption from Game Based Crypto *)
fun dec_list :: "'grp priv_key \<Rightarrow> 'grp cipher list \<Rightarrow> 'grp list option"
  where
    "dec_list _ [] = Some []" |
    "dec_list priv_key (x # xs) = (case adecrypt priv_key x of
      None \<Rightarrow> None |
      Some val_x \<Rightarrow> (case dec_list priv_key xs of
                      None \<Rightarrow> None |
                      Some dec_xs \<Rightarrow> Some (val_x # dec_xs)))"*)


end

end