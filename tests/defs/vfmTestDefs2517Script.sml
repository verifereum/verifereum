open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2517";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroCallsRevert/ZeroValue_DELEGATECALL_OOGRevert.json";
val defs = mapi (define_test "2517") tests;
val () = export_theory_no_docs ();
