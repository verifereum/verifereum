open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0214";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7939_count_leading_zeros/test_clz_jump_operation.json";
val defs = mapi (define_test "0214") tests;
val () = export_theory_no_docs ();
