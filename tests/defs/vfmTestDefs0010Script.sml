open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0010";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/test_basic_tload_after_store.json";
val defs = mapi (define_test "0010") tests;
val () = export_theory_no_docs ();
