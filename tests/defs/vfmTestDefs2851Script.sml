Theory vfmTestDefs2851[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stWalletTest/multi_owned_change_owner_to_is_owner/multi_owned_change_owner_to_is_owner.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stWalletTest/multi_owned_change_owner_to_is_owner/multi_owned_change_owner_to_is_owner.json");
val defs = mapi (define_test "2851") tests;
