Theory vfmTestDefs1020[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/constantinople/eip1052_extcodehash/extcodehash/extcodecopy_zero_code.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/constantinople/eip1052_extcodehash/extcodehash/extcodecopy_zero_code.json");
val defs = mapi (define_test "1020") tests;
