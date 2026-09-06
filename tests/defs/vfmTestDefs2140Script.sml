Theory vfmTestDefs2140[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stWalletTest/multi_owned_add_owner/multi_owned_add_owner.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stWalletTest/multi_owned_add_owner/multi_owned_add_owner.json");
val defs = mapi (define_test "2140") tests;
