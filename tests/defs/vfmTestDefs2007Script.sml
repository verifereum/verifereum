open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2007";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/PythonRevertTestTue201814-1430.json";
val defs = mapi (define_test "2007") tests;
val () = export_theory_no_docs ();
