open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1093";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/TransactionCreateStopInInitcode.json";
val defs = mapi (define_test "1093") tests;
val () = export_theory_no_docs ();
