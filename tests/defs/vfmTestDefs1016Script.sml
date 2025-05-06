open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1016";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP2930/variedContext.json";
val defs = mapi (define_test "1016") tests;
val () = export_theory_no_docs ();
