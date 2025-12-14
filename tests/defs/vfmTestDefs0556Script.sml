open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0556";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcallcode_ABCB_RECURSIVE.json";
val defs = mapi (define_test "0556") tests;
val () = export_theory_no_docs ();
