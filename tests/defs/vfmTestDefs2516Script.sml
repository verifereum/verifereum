Theory vfmTestDefs2516[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/multiOwnedChangeRequirementTo2.json";
val defs = mapi (define_test "2516") tests;
