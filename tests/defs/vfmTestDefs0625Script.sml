open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0625";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/callOutput2.json";
val defs = mapi (define_test "0625") tests;
val () = export_theory_no_docs ();
