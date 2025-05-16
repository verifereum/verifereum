open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2013";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSolidityTest/RecursiveCreateContractsCreate4Contracts.json";
val defs = mapi (define_test "2013") tests;
val () = export_theory_no_docs ();
