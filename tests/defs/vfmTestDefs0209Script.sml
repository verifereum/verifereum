Theory vfmTestDefs0209[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/osaka/eip7939_count_leading_zeros/test_clz_from_set_code.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/osaka/eip7939_count_leading_zeros/test_clz_from_set_code.json");
val defs = mapi (define_test "0209") tests;
