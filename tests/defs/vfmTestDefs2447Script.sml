open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2447";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTransactionTest/StoreClearsAndInternalCallStoreClearsOOG.json";
val defs = mapi (define_test "2447") tests;
val () = export_theory_no_docs ();
