open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0549";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/callcodeOutput3Fail.json";
val defs = mapi (define_test "0549") tests;
val () = export_theory_no_docs ();
