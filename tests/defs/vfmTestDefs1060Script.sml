open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1060";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashDynamicArgument.json";
val defs = mapi (define_test "1060") tests;
val () = export_theory_no_docs ();
