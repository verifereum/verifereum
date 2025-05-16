open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0725";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/call_outsize_then_create2_successful_then_returndatasize.json";
val defs = mapi (define_test "0725") tests;
val () = export_theory_no_docs ();
