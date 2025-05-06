open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2551";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/InternalCallHittingGasLimitSuccess.json";
val defs = mapi (define_test "2551") tests;
val () = export_theory_no_docs ();
