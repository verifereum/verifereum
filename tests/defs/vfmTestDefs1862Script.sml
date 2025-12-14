open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1862";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refund50_2.json";
val defs = mapi (define_test "1862") tests;
val () = export_theory_no_docs ();
