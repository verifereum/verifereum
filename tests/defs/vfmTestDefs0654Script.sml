open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0654";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/callOutput3partialFail.json";
val defs = mapi (define_test "0654") tests;
val () = export_theory_no_docs ();
