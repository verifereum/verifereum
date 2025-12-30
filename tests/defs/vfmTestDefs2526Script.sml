Theory vfmTestDefs2526[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/multiOwnedRevokeNothing.json";
val defs = mapi (define_test "2526") tests;
