theory verifyPlurality imports
"Game_Based_Crypto.Elgamal"
begin

context elgamal_base
begin

fun ballotEncrypt :: "'grp pub_key \<Rightarrow> 'grp list \<Rightarrow> 'grp cipher spmf list" 
  where
   ballotEncryptNil: "ballotEncrypt pk [] = []" |
   ballotEncryptCons: "ballotEncrypt pk (x # xs) = (aencrypt pk x) # ballotEncrypt pk xs"

fun ballotDecrypt :: "'grp priv_key \<Rightarrow> 'grp cipher list \<Rightarrow> 'grp option list"
  where 
    ballotDecryptNil: "ballotDecrypt sk [] = []" |
    ballotDecryptCons: "ballotDecrypt sk (x # xs) = (adecrypt sk x) # ballotDecrypt sk xs"

(*lemma enc_dec:
    "ballotEncrypt pub_key (ballotDecrypt priv_key xs) = xs"*)
(*lemma dec_enc:
    "ballotDecrypt priv_key (ballotEncrypt pub_key xs) = xs"*)

end

end