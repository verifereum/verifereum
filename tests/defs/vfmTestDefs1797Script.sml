open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1797";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest628.json";
val defs = mapi (define_test "1797") tests;
val () = export_theory_no_docs ();
