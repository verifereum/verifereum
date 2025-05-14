open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1008";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP158Specific/CALL_ZeroVCallSuicide.json";
val defs = mapi (define_test "1008") tests;
val () = export_theory_no_docs ();
