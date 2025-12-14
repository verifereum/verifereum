open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1049";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/OutOfGasPrefundedContractCreation.json";
val defs = mapi (define_test "1049") tests;
val () = export_theory_no_docs ();
