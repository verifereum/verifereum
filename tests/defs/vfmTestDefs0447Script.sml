open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0447";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBugs/returndatacopyPythonBug_Tue_03_48_41-1432.json";
val defs = mapi (define_test "0447") tests;
val () = export_theory_no_docs ();
