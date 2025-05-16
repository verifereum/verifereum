open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2434";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/HighGasPriceParis.json";
val defs = mapi (define_test "2434") tests;
val () = export_theory_no_docs ();
