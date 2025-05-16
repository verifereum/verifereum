open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1889";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/PythonRevertTestTue201814-1430.json";
val defs = mapi (define_test "1889") tests;
val () = export_theory_no_docs ();
