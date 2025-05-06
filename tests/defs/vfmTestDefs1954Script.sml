open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1954";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refund_multimpleSuicide.json";
val defs = mapi (define_test "1954") tests;
val () = export_theory_no_docs ();
