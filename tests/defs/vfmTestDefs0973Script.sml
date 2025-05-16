open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0973";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/TransactionCreateAutoSuicideContract.json";
val defs = mapi (define_test "0973") tests;
val () = export_theory_no_docs ();
