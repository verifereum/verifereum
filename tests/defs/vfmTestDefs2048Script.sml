open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2048";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSolidityTest/CreateContractFromMethod.json";
val defs = mapi (define_test "2048") tests;
val () = export_theory_no_docs ();
