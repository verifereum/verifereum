open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1827";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refundSuicide50procentCap.json";
val defs = mapi (define_test "1827") tests;
val () = export_theory_no_docs ();
