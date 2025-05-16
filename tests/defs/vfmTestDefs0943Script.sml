open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0943";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashInInitCode.json";
val defs = mapi (define_test "0943") tests;
val () = export_theory_no_docs ();
