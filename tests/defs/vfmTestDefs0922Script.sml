open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0922";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/createEmptyThenExtcodehash.json";
val defs = mapi (define_test "0922") tests;
val () = export_theory_no_docs ();
