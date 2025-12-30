Theory vfmTestDefs2685[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_bad_length_193.json";
val defs = mapi (define_test "2685") tests;
