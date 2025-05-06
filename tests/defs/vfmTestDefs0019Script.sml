open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0019";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/tstorage_execution_contexts/subcall.json";
val defs = mapi (define_test "0019") tests;
val () = export_theory_no_docs ();
