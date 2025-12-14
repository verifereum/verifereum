open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2023";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shl01.json";
val defs = mapi (define_test "2023") tests;
val () = export_theory_no_docs ();
