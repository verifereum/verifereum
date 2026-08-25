Theory vfmTestDefs2512[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stWalletTest/multiOwnedChangeOwner_fromNotOwner.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stWalletTest/multiOwnedChangeOwner_fromNotOwner.json");
val defs = mapi (define_test "2512") tests;
