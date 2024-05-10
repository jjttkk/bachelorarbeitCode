theory verifyPlurality imports
"Game_Based_Crypto.Elgamal"
begin

context elgamal_base
begin

fun ballotEncrypt :: "'grp pub_key \<Rightarrow> 'grp list \<Rightarrow> 'grp cipher spmf list" 
  where
    "ballotEncrypt pk [] = []" |
    "ballotEncrypt pk (x # xs) = (aencrypt pk x) # ballotEncrypt pk xs"

definition ballot_aencrypt :: "'grp pub_key \<Rightarrow> 'grp list \<Rightarrow> 'grp cipher spmf list"
where
  "ballot_aencrypt pk (x # xs) = do {
   return_spmf (aencrypt pk x # ballot_aencrypt pk xs)
  }"

definition ballot_adecrypt :: "'grp priv_key \<Rightarrow> 'grp cipher spmf list \<Rightarrow> 'grp option list"
where
  "ballot_adecrypt x = (\<lambda>(\<beta>, \<zeta>). Some (\<zeta> \<otimes> (inv (\<beta> [^] x))))"

(*fun ballotDecrypt :: "'grp priv_key \<Rightarrow> 'grp cipher spmf list \<Rightarrow> 'grp option list"
  where 
    "ballotDecrypt sk xss = xss \<bind> (\<lambda>xs. map (\<lambda>y. adecrypt sk y))"*) (* do {
      xs \<leftarrow> xss
      map (\<lambda>x. adecrypt sk x) xs
    }"*)
    
fun ballotDecrypt :: "'grp priv_key \<Rightarrow> 'grp cipher list \<Rightarrow> 'grp option list"
  where 
    ballotDecryptNil: "ballotDecrypt sk [] = []" |
    ballotDecryptCons: "ballotDecrypt sk (x # xs) = (adecrypt sk x) # ballotDecrypt sk xs"

lemma enc_dec: "aencrypt pk (adecrypt sk x) = x"

lemma dec_enc: "adecrypt sk (aencrypt pk y) = y"

theorem ballot_enc_dec: "ballotEncrypt pk (ballotDecrypt sk xs) = xs"
  apply (induct xs)
  apply auto

(*lemma dec_enc:
    "ballotDecrypt sk (ballotEncrypt pk ys) = ys"*)

(*lemma enc_dec: "aencrypt pk (adecrypt sk x) = x"

lemma dec_enc: "adecrypt sk (aencrypt pk y) = y"*)

theorem ballot_enc_dec: "ballotEncrypt pk (ballotDecrypt sk xs) = xs"


(*lemma dec_enc:
    "ballotDecrypt sk (ballotEncrypt pk ys) = ys"*)

end

end