open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2453";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/SuicidesAndInternalCallSuicidesSuccess.json";
val defs = mapi (define_test "2453") tests;
val () = export_theory_no_docs ();
