open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1885";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/call_then_call_value_fail_then_returndatasize.json";
val defs = mapi (define_test "1885") tests;
val () = export_theory_no_docs ();
