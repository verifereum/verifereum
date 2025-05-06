open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1236";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mem64kb_singleByte.json";
val defs = mapi (define_test "1236") tests;
val () = export_theory_no_docs ();
