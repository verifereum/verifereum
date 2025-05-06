open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1061";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashPrecompiles.json";
val defs = mapi (define_test "1061") tests;
val () = export_theory_no_docs ();
