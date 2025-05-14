open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1960";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/call_ecrec_success_empty_then_returndatasize.json";
val defs = mapi (define_test "1960") tests;
val () = export_theory_no_docs ();
