Theory vfmTestDefs1016[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/constantinople/eip1014_create2/create2_revert/create2_succeeds_after_reverted_create2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/constantinople/eip1014_create2/create2_revert/create2_succeeds_after_reverted_create2.json");
val defs = mapi (define_test "1016") tests;
