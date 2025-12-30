Theory vfmTestDefs2512[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/multiOwnedChangeOwner_fromNotOwner.json";
val defs = mapi (define_test "2512") tests;
