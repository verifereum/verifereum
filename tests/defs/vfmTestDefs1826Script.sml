open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1826";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRefundTest/refundSSTORE.json";
val defs = mapi (define_test "1826") tests;
val () = export_theory_no_docs ();
