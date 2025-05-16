open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0944";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashMaxCodeSize.json";
val defs = mapi (define_test "0944") tests;
val () = export_theory_no_docs ();
