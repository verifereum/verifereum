open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1879";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatasize_initial_zero_read.json";
val defs = mapi (define_test "1879") tests;
val () = export_theory_no_docs ();
