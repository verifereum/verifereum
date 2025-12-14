open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2443";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/suicideCallerAddresTooBigLeft.json";
val defs = mapi (define_test "2443") tests;
val () = export_theory_no_docs ();
