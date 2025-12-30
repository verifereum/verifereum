Theory vfmTestDefs0850[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/CREATE_HighNonce.json";
val defs = mapi (define_test "0850") tests;
