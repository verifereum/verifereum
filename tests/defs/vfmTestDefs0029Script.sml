open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0029";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/test_tstore_reentrancy.json";
val defs = mapi (define_test "0029") tests;
val () = export_theory_no_docs ();
