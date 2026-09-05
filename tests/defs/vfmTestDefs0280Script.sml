Theory vfmTestDefs0280[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/osaka/eip7939_count_leading_zeros/count_leading_zeros/clz_opcode_scenarios.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/osaka/eip7939_count_leading_zeros/count_leading_zeros/clz_opcode_scenarios.json");
val defs = mapi (define_test "0280") tests;
