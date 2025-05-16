open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0570";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/createNameRegistratorendowmentTooHigh.json";
val defs = mapi (define_test "0570") tests;
val () = export_theory_no_docs ();
