open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0701";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/CREATE2_HighNonce.json";
val defs = mapi (define_test "0701") tests;
val () = export_theory_no_docs ();
