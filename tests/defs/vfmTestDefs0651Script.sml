open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0651";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/callOutput3.json";
val defs = mapi (define_test "0651") tests;
val () = export_theory_no_docs ();
