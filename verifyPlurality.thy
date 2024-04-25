theory verifyPlurality imports
"afp/thys/Game_Based_Crypto/Elgamal"
begin

type_synonym 'a' pub_key = "'a'"
type_synonym 'a' priv_key = nat
type_synonym 'a' plain = 'a'
type_synonym 'a' cipher = "'a' \<times> 'a'"

fun ballotEncrypt :: "'a pub_key \<Rightarrow> 'a list \<Rightarrow> 'a cipher list spmf" 
  where
   ballotEncryptNil: "ballotEncrypt [] = []" |
   ballotEncryptCons: "ballotEncrypt (x # xs) = (aencrypt pub_key x) # ballotEncrypt pub_key  xs"

fun ballotDecrypt :: "'a priv_key \<Rightarrow> 'a cipher list \<Rightarrow> 'a option"
  where 
    ballotDecryptNil: "ballotDecrypt [] = []" |
    ballotDecryptCons: "ballotDecrypt (x # xs) = (adecrypt priv_key x) # ballotDecrypt priv_key xs"

(*lemma enc_dec:
    "ballotEncrypt pub_key (ballotDecrypt priv_key xs) = xs"*)
(*lemma dec_enc:
    "ballotDecrypt priv_key (ballotEncrypt pub_key xs) = xs"*)

end