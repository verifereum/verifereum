open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1834";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refund_NoOOG_1.json";
val defs = mapi (define_test "1834") tests;
val () = export_theory_no_docs ();
