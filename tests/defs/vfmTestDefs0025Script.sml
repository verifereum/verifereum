open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0025";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/test_tload_reentrancy.json";
val defs = mapi (define_test "0025") tests;
val () = export_theory_no_docs ();
