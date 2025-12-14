open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1000";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/callToSuicideThenExtcodehash.json";
val defs = mapi (define_test "1000") tests;
val () = export_theory_no_docs ();
