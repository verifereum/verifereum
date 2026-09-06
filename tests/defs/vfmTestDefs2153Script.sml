Theory vfmTestDefs2153[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stWalletTest/multi_owned_is_owner_true/multi_owned_is_owner_true.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stWalletTest/multi_owned_is_owner_true/multi_owned_is_owner_true.json");
val defs = mapi (define_test "2153") tests;
