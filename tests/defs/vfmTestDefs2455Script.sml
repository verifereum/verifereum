open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2455";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/SuicidesStopAfterSuicide.json";
val defs = mapi (define_test "2455") tests;
val () = export_theory_no_docs ();
