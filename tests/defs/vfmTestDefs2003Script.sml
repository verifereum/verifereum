open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2003";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shr_2^255_256.json";
val defs = mapi (define_test "2003") tests;
val () = export_theory_no_docs ();
