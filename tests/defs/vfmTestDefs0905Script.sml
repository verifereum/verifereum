open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0905";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreateTest/createFailResult.json";
val defs = mapi (define_test "0905") tests;
val () = export_theory_no_docs ();
