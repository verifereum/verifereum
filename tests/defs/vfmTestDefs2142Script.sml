open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2142";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSpecialTest/JUMPDEST_AttackwithJump.json";
val defs = mapi (define_test "2142") tests;
val () = export_theory_no_docs ();
