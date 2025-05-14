open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0006";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/basic_tload/basic_tload_other_after_tstore.json";
val defs = mapi (define_test "0006") tests;
val () = export_theory_no_docs ();
