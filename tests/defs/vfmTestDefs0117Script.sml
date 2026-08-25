Theory vfmTestDefs0117[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/constantinople/eip145_bitwise_shift/test_combinations.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/constantinople/eip145_bitwise_shift/test_combinations.json");
val defs = mapi (define_test "0117") tests;
