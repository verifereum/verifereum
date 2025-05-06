open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2524";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/suicideSendEtherPostDeath.json";
val defs = mapi (define_test "2524") tests;
val () = export_theory_no_docs ();
