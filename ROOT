(*
 *  cd ..../theories
 *
 *  isabelle build -b -P "output" -D `pwd`
 *    # compile sessions in the ROOT file to prebuilt images
 *
 *  isabelle build -o quick_and_dirty -b -P "output" -D `pwd`
 *    # compile albeit "sorry"s
 *
 *  isabelle jedit -d `pwd` -l verifyPlurality
 *    # use an image for interactive mode; probably similar for servermode.
 *
 * Theories can then be accessed as, e.g., "Verified_Voting_Rule_Construction.Preference_Relation"
 *)

chapter browser_info

session verifyPlurality = HOL +
  description
    \<open>Verified Construction of Fair Voting Rules\<close>
  options [timeout = 400, browser_info, document = pdf, document_output = "output",
            document_variants = "document:outline=/proof,/ML"]

  sessions
    "Verified_Voting_Rule_Construction"
    
  directories
    "afp/thys"
    "afp/thys/Game_Based_Crypto"
    "afp/thys/verifiedVotingRuleConstruction"
    "afp/thys/verifiedVotingRuleConstruction/theories"

  theories
    "afp/thys/Game_Based_Crypto/Elgamal"
    "afp/thys/verifiedVotingRuleConstruction/theories/Plurality_Rule"


  document_files
  
