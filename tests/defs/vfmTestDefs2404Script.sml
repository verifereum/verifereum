open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2404";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/suicideAddress.json";
val defs = mapi (define_test "2404") tests;
val () = export_theory_no_docs ();
