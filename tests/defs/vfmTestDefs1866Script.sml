open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1866";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refundMax.json";
val defs = mapi (define_test "1866") tests;
val () = export_theory_no_docs ();
