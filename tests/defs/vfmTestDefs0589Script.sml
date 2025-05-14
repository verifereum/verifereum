open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0589";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcodecall_010.json";
val defs = mapi (define_test "0589") tests;
val () = export_theory_no_docs ();
