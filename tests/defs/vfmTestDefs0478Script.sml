Theory vfmTestDefs0478[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmTests/sha3.json";
val defs = mapi (define_test "0478") tests;
