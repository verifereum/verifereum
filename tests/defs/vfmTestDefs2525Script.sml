open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2525";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/suicideCallerAddresTooBigRight.json";
val defs = mapi (define_test "2525") tests;
val () = export_theory_no_docs ();
