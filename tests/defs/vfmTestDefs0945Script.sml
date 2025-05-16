open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0945";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashNewAccount.json";
val defs = mapi (define_test "0945") tests;
val () = export_theory_no_docs ();
