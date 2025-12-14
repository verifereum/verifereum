open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1040";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/CallContractToCreateContractAndCallItOOG.json";
val defs = mapi (define_test "1040") tests;
val () = export_theory_no_docs ();
