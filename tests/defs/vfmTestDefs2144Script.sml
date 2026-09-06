Theory vfmTestDefs2144[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stWalletTest/multi_owned_change_owner_no_argument/multi_owned_change_owner_no_argument.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stWalletTest/multi_owned_change_owner_no_argument/multi_owned_change_owner_no_argument.json");
val defs = mapi (define_test "2144") tests;
