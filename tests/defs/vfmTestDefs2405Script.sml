open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2405";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/suicideCaller.json";
val defs = mapi (define_test "2405") tests;
val () = export_theory_no_docs ();
