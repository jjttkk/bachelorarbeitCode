theory verifyPlurality imports
"Game_Based_Crypto.Elgamal"
begin

context ind_cpa
begin

fun ballotEncrypt :: "'grp pub_key \<Rightarrow> 'a list \<Rightarrow> 'a cipher list spmf" 
  where
   ballotEncryptNil: "ballotEncrypt pk [] = []" |
   ballotEncryptCons: "ballotEncrypt (x # xs) = (aencrypt pk x) # ballotEncrypt pk  xs"

fun ballotDecrypt :: "'a priv_key \<Rightarrow> 'a cipher list \<Rightarrow> 'a option"
  where 
    ballotDecryptNil: "ballotDecrypt [] = []" |
    ballotDecryptCons: "ballotDecrypt (x # xs) = (adecrypt priv_key x) # ballotDecrypt priv_key xs"

(*lemma enc_dec:
    "ballotEncrypt pub_key (ballotDecrypt priv_key xs) = xs"*)
(*lemma dec_enc:
    "ballotDecrypt priv_key (ballotEncrypt pub_key xs) = xs"*)

end