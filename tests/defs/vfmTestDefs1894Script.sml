open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1894";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertInCreateInInit_Paris.json";
val defs = mapi (define_test "1894") tests;
val () = export_theory_no_docs ();
