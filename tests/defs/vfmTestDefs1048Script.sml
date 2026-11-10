Theory vfmTestDefs1048[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/frontier/create/create_deposit_oog/create_deposit_oog.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/frontier/create/create_deposit_oog/create_deposit_oog.json");
val defs = mapi (define_test "1048") tests;
