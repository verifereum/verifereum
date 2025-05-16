open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2435";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/InternalCallHittingGasLimit.json";
val defs = mapi (define_test "2435") tests;
val () = export_theory_no_docs ();
