open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2433";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/HighGasLimit.json";
val defs = mapi (define_test "2433") tests;
val () = export_theory_no_docs ();
