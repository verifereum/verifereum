open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0876";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stDelegatecallTestHomestead/Call1024BalanceTooLow.json";
val defs = mapi (define_test "0876") tests;
val () = export_theory_no_docs ();
