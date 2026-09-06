Theory vfmTestDefs2089[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/suicide_not_existing_account/suicide_not_existing_account.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stSystemOperationsTest/suicide_not_existing_account/suicide_not_existing_account.json");
val defs = mapi (define_test "2089") tests;
