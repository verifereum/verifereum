open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0940";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150Specific/CallAskMoreGasOnDepth2ThenTransactionHas.json";
val defs = mapi (define_test "0940") tests;
val () = export_theory_no_docs ();
