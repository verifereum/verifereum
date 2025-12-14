open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0627";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/callOutput3Fail.json";
val defs = mapi (define_test "0627") tests;
val () = export_theory_no_docs ();
