Theory vfmTestDefs2862[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stWalletTest/multi_owned_remove_owner_my_self/multi_owned_remove_owner_my_self.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stWalletTest/multi_owned_remove_owner_my_self/multi_owned_remove_owner_my_self.json");
val defs = mapi (define_test "2862") tests;
