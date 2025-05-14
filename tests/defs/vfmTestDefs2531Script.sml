open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2531";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTimeConsuming/CALLBlake2f_MaxRounds.json";
val defs = mapi (define_test "2531") tests;
val () = export_theory_no_docs ();
