open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1050";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/ReturnTest.json";
val defs = mapi (define_test "1050") tests;
val () = export_theory_no_docs ();
