open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0562";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/createInitFail_OOGduringInit.json";
val defs = mapi (define_test "0562") tests;
val () = export_theory_no_docs ();
