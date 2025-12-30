Theory vfmTestDefs2518[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/multiOwnedConstructionNotEnoughGas.json";
val defs = mapi (define_test "2518") tests;
