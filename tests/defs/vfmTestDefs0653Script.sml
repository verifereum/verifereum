open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0653";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/callOutput1.json";
val defs = mapi (define_test "0653") tests;
val () = export_theory_no_docs ();
