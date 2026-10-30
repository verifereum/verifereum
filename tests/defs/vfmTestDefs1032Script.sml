Theory vfmTestDefs1032[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/constantinople/eip1052_extcodehash/extcodehash/extcodehash_empty_send_value.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/constantinople/eip1052_extcodehash/extcodehash/extcodehash_empty_send_value.json");
val defs = mapi (define_test "1032") tests;
