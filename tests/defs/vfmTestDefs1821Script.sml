open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1821";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest604.json";
val defs = mapi (define_test "1821") tests;
val () = export_theory_no_docs ();
