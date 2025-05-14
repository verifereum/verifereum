open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1913";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom2/randomStatetest626.json";
val defs = mapi (define_test "1913") tests;
val () = export_theory_no_docs ();
