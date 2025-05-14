open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1009";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP158Specific/EXP_Empty.json";
val defs = mapi (define_test "1009") tests;
val () = export_theory_no_docs ();
