open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1955";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refund_singleSuicide.json";
val defs = mapi (define_test "1955") tests;
val () = export_theory_no_docs ();
