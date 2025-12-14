open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0210";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7939_count_leading_zeros/test_clz_gas_cost.json";
val defs = mapi (define_test "0210") tests;
val () = export_theory_no_docs ();
