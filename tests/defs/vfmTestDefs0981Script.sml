open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0981";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log0_nonEmptyMem.json";
val defs = mapi (define_test "0981") tests;
val () = export_theory_no_docs ();
