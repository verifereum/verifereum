open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1200";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mem64kb_singleByte-32.json";
val defs = mapi (define_test "1200") tests;
val () = export_theory_no_docs ();
