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
 * *)

chapter browser_info

session verifyPlurality = HOL + Game_Based_Crypto + Verified_Voting_Rule_Construction
description
    \<open>verify plurality voting rule\<close>
  options [timeout = 400, browser_info, document = pdf, document_output = "output",
            document_variants = "document:outline=/proof,/ML"]
  sessions
    "HOL-Library"
    "HOL-Analysis"
    "HOL-Combinatorics"
    "HOL-Algebra"
    "List-Index"
    "Collections"
 
  directories
    "afp/thys"
    "afp/thys/Game_Based_Crypto"
    "afp/thys/verifiedVotingRuleConstruction"
    "afp/thys/verifiedVotingRuleConstruction/theories"

  theories
    "Game_Based_Crypto"
    "verifiedVotingRuleConstruction"
    "afp/thys/Game_Based_Crypto/Elgamal"
    "afp/thys/verifiedVotingRuleConstruction/theories/Plurality_Rule"

  document_files
    "root.tex"
    "settings.tex"
    "root.bib"
 
