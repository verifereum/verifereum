open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1129";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryTest/mstroe8_dejavu.json";
val defs = mapi (define_test "1129") tests;
val () = export_theory_no_docs ();
