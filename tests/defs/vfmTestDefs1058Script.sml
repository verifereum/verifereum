open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1058";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashMaxCodeSize.json";
val defs = mapi (define_test "1058") tests;
val () = export_theory_no_docs ();
