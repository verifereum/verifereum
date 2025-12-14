open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0023";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/test_tload_after_tstore_is_zero.json";
val defs = mapi (define_test "0023") tests;
val () = export_theory_no_docs ();
