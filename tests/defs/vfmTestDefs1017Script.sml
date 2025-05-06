open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1017";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP3607/initCollidingWithNonEmptyAccount.json";
val defs = mapi (define_test "1017") tests;
val () = export_theory_no_docs ();
