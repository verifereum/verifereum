open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1957";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/call_outsize_then_create_successful_then_returndatasize.json";
val defs = mapi (define_test "1957") tests;
val () = export_theory_no_docs ();
