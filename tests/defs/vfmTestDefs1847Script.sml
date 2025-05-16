open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1847";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/create_callprecompile_returndatasize.json";
val defs = mapi (define_test "1847") tests;
val () = export_theory_no_docs ();
