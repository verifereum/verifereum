open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0213";
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7939_count_leading_zeros/test_clz_initcode_create.json";
val defs = mapi (define_test "0213") tests;
val () = export_theory_no_docs ();
