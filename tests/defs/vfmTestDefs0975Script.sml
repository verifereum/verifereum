open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0975";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP158Specific/callToEmptyThenCallErrorParis.json";
val defs = mapi (define_test "0975") tests;
val () = export_theory_no_docs ();
