open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2413";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stTimeConsuming/CALLBlake2f_MaxRounds.json";
val defs = mapi (define_test "2413") tests;
val () = export_theory_no_docs ();
