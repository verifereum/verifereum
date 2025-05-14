open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1014";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP2930/addressOpcodes.json";
val defs = mapi (define_test "1014") tests;
val () = export_theory_no_docs ();
