open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0948";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashSTATICCALL.json";
val defs = mapi (define_test "0948") tests;
val () = export_theory_no_docs ();
