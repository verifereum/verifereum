open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0903";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP3607/initCollidingWithNonEmptyAccount.json";
val defs = mapi (define_test "0903") tests;
val () = export_theory_no_docs ();
