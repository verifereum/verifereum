open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1013";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashDELEGATECALL.json";
val defs = mapi (define_test "1013") tests;
val () = export_theory_no_docs ();
