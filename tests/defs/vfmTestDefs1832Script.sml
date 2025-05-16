open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1832";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refund_CallToSuicideStorage.json";
val defs = mapi (define_test "1832") tests;
val () = export_theory_no_docs ();
