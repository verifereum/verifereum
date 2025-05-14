open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0680";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/createInitFail_OOGduringInit2.json";
val defs = mapi (define_test "0680") tests;
val () = export_theory_no_docs ();
