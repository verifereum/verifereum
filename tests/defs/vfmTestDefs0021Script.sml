open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0021";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/tstorage_reentrancy_contexts/reentrant_call.json";
val defs = mapi (define_test "0021") tests;
val () = export_theory_no_docs ();
