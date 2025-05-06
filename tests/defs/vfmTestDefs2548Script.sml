open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2548";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/HighGasPriceParis.json";
val defs = mapi (define_test "2548") tests;
val () = export_theory_no_docs ();
