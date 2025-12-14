open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2471";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/InternalCallHittingGasLimit2.json";
val defs = mapi (define_test "2471") tests;
val () = export_theory_no_docs ();
