theory verifyEncryptionDecryption imports
"Game_Based_Crypto.Elgamal"
begin

context elgamal_base
begin

(*Function to encrypt a list of elements using Elgamal-Encryption from Game Based Crypto*)
definition enc_list:: "'grp pub_key \<Rightarrow> 'grp list \<Rightarrow> 'grp cipher spmf list"
  where "enc_list \<alpha> ls = (map (aencrypt \<alpha>) ls)"

(*Function to decrypt a list of elements using Elgamal-Decryption from Game Based Crypto*)
definition dec_list :: "'grp priv_key \<Rightarrow> 'grp cipher spmf list \<Rightarrow> 'grp option spmf list" 
where
 "dec_list \<beta> ciphers = map (\<lambda>c. map_spmf (adecrypt \<beta>) c) ciphers"

(*Functions to parse the type for proving the lemmas*)
definition fix_type:: "'grp list \<Rightarrow> 'grp option spmf list"
  where "fix_type xs = map (\<lambda>x. return_spmf (Some x)) xs" 

definition fix_type_single:: "'grp \<Rightarrow> 'grp option spmf"
  where "fix_type_single x = return_spmf (Some x)"


lemma decrypt_encrypt_list:
  assumes "\<forall>x. decrypt (encrypt pk x) = return_spmf (Some x)"
  shows "dec_list sk (enc_list pk (l # ls)) = fix_type (l # ls)"
  using assms
  apply (induction ls arbitrary: l)
   apply (simp add: dec_list_def enc_list_def fix_type_def map_spmf_bind_spmf aencrypt_def adecrypt_def)
   apply (auto simp add: dec_list_def enc_list_def fix_type_def map_spmf_bind_spmf aencrypt_def adecrypt_def)
  apply (metis (no_types, lifting) spmf.map_comp o_def)
  done



end

end