open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0882";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP1559/outOfFundsOldTypes.json";
val defs = mapi (define_test "0882") tests;
val () = export_theory_no_docs ();
