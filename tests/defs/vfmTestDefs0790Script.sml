open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0790";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/CREATE2_HighNonceDelegatecall.json";
val defs = mapi (define_test "0790") tests;
val () = export_theory_no_docs ();
