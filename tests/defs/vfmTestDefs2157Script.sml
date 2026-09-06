Theory vfmTestDefs2157[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stWalletTest/multi_owned_remove_owner_owner_is_not_owner/multi_owned_remove_owner_owner_is_not_owner.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stWalletTest/multi_owned_remove_owner_owner_is_not_owner/multi_owned_remove_owner_owner_is_not_owner.json");
val defs = mapi (define_test "2157") tests;
