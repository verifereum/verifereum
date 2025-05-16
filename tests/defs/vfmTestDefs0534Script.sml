open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0534";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/Callcode1024OOG.json";
val defs = mapi (define_test "0534") tests;
val () = export_theory_no_docs ();
