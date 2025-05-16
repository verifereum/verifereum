open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0446";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stBugs/randomStatetestDEFAULT-Tue_07_58_41-15153-575192_london.json";
val defs = mapi (define_test "0446") tests;
val () = export_theory_no_docs ();
