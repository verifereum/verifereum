open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0964";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/CallContractToCreateContractWhichWouldCreateContractIfCalled.json";
val defs = mapi (define_test "0964") tests;
val () = export_theory_no_docs ();
