open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2593";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stWalletTest/multiOwnedChangeRequirementTo0.json";
val defs = mapi (define_test "2593") tests;
val () = export_theory_no_docs ();
