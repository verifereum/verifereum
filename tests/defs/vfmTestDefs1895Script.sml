open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1895";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertInDelegateCall.json";
val defs = mapi (define_test "1895") tests;
val () = export_theory_no_docs ();
