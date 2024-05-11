theory verifyEncryptionDecryption imports
"Game_Based_Crypto.Elgamal"
begin

context elgamal_base
begin

(*Function to encrypt a list of elements using Elgamal-Encryption from Game Based Crypto*)
fun enc_list:: "'grp pub_key \<Rightarrow> 'grp list \<Rightarrow> 'grp cipher spmf list"
  where "enc_list \<alpha> ls = (map (aencrypt \<alpha>) ls)"

(*Function to decrypt a list of elements using Elgamal-Decryption from Game Based Crypto*)
fun dec_list :: "'grp priv_key \<Rightarrow> 'grp cipher spmf list \<Rightarrow> 'grp option spmf list" 
where
 "dec_list \<beta> ciphers = map (\<lambda>c. map_spmf (adecrypt \<beta>) c) ciphers"

(*Function to parse the type for proving*)
fun fix_type:: "'grp list \<Rightarrow> 'grp option spmf list"
  where "fix_type xs = map (\<lambda>x. return_spmf (Some x)) xs" 


(*x option spmf = dec (enc x)*)

lemma encrypt_then_decrypt_same_message: 
  assumes "msg \<in> carrier \<G>" 
  shows "adecrypt x (aencrypt \<alpha> msg) = Some msg"
proof -
  have "adecrypt x (aencrypt \<alpha> msg) = adecrypt x (\<^bold>g [^] y, (\<alpha> [^] y) \<otimes> msg)"
    unfolding aencrypt_def adecrypt_def by simp
  also have "... = Some (((\<alpha> [^] y) \<otimes> msg) \<otimes> (inv (\<^bold>g [^] y [^] x)))"
    using assms unfolding aencrypt_def adecrypt_def by simp
  also have "... = Some (((\<alpha> [^] y) \<otimes> msg) \<otimes> (\<^bold>g [^] (y * x)))"
    using assms by (simp add: nat_pow_mult)
  also have "... = Some (msg \<otimes> (\<^bold>g [^] (y * x)))"
    using assms by (simp add: m_assoc)
  also have "... = Some msg" 
    using assms by (simp add: nat_pow_pow)
  finally show ?thesis .
qed

definition \<alpha> :: "'grp pub_key" where "\<alpha> = g [^] x"
 
lemma aencrypt_adecrypt:
  "adecrypt x (aencrypt \<alpha> msg) = Some msg"
proof -
  have "adecrypt x (aencrypt \<alpha> msg) = Some (snd (aencrypt \<alpha> msg) \<otimes> inv (fst (aencrypt \<alpha> msg) [^] x))"
    by (simp add: aencrypt_def adecrypt_def)
  also have "... = Some (((\<alpha> [^] y) \<otimes> msg) \<otimes> inv ((g [^] y) [^] x))"
    by (simp add: \<alpha>_def)
  also have "... = Some (g [^] (x * y) \<otimes> msg \<otimes> inv (g [^] (y * x)))"
    by (simp add: pow_mult_distrib)
  also have "... = Some (g [^] 0 \<otimes> msg)"
    by (simp add: pow_mult_inverse)
  also have "... = Some msg"
    by (simp add: pow_zero_ident mult_assoc)
  finally show ?thesis .
qed

(*lemma dec_enc: "adecrypt sk (aencrypt pk y) = y"

theorem ballot_enc_dec: "ballotEncrypt pk (ballotDecrypt sk xs) = xs"
  apply (induct xs)
  apply auto

lemma dec_enc:
    "ballotDecrypt sk (ballotEncrypt pk ys) = ys"

lemma enc_dec: "aencrypt pk (adecrypt sk x) = x"

lemma dec_enc: "adecrypt sk (aencrypt pk y) = y"

theorem ballot_enc_dec: "ballotEncrypt pk (ballotDecrypt sk xs) = xs"

lemma dec_enc:
    "ballotDecrypt sk (ballotEncrypt pk ys) = ys"*)

end

end