open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0703";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/CREATE2_HighNonceMinus1.json";
val defs = mapi (define_test "0703") tests;
val () = export_theory_no_docs ();
