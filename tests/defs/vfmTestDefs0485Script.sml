open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0485";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcodecallcode_ABCB_RECURSIVE.json";
val defs = mapi (define_test "0485") tests;
val () = export_theory_no_docs ();
