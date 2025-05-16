open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2014";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSolidityTest/TestBlockAndTransactionProperties.json";
val defs = mapi (define_test "2014") tests;
val () = export_theory_no_docs ();
