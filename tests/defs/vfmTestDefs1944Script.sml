open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1944";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refund_CallA_notEnoughGasInCall.json";
val defs = mapi (define_test "1944") tests;
val () = export_theory_no_docs ();
