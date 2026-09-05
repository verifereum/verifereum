Theory vfmTestDefs0166[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/constantinople/eip1052_extcodehash/extcodehash/extcodehash_via_call.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/constantinople/eip1052_extcodehash/extcodehash/extcodehash_via_call.json");
val defs = mapi (define_test "0166") tests;
