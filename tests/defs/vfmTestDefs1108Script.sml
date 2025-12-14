open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1108";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemExpandingEIP150Calls/DelegateCallOnEIPWithMemExpandingCalls.json";
val defs = mapi (define_test "1108") tests;
val () = export_theory_no_docs ();
