open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1074";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/CallContractToCreateContractAndCallItOOG.json";
val defs = mapi (define_test "1074") tests;
val () = export_theory_no_docs ();
