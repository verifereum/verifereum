open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2010";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertInStaticCall.json";
val defs = mapi (define_test "2010") tests;
val () = export_theory_no_docs ();
