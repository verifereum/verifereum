open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0552";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/callcodeWithHighValue.json";
val defs = mapi (define_test "0552") tests;
val () = export_theory_no_docs ();
