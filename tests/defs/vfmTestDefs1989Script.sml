open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1989";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatasize_after_failing_staticcall.json";
val defs = mapi (define_test "1989") tests;
val () = export_theory_no_docs ();
