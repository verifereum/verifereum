open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0889";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP158Specific/CALL_OneVCallSuicide2.json";
val defs = mapi (define_test "0889") tests;
val () = export_theory_no_docs ();
