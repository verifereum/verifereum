open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0027";
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/test_tstore_clear_after_deployment_tx.json";
val defs = mapi (define_test "0027") tests;
val () = export_theory_no_docs ();
