open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0022";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/tstorage_selfdestruct/reentrant_selfdestructing_call.json";
val defs = mapi (define_test "0022") tests;
val () = export_theory_no_docs ();
