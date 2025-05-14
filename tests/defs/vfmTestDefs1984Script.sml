open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1984";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatacopy_initial_256.json";
val defs = mapi (define_test "1984") tests;
val () = export_theory_no_docs ();
