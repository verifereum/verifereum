open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1043";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/CallContractToCreateContractOOGBonusGas.json";
val defs = mapi (define_test "1043") tests;
val () = export_theory_no_docs ();
