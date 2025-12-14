open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1187";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mem64kb+32.json";
val defs = mapi (define_test "1187") tests;
val () = export_theory_no_docs ();
