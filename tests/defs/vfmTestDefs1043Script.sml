Theory vfmTestDefs1043[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/constantinople/eip145_bitwise_shift/shift_combinations/combinations.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/constantinople/eip145_bitwise_shift/shift_combinations/combinations.json");
val defs = mapi (define_test "1043") tests;
