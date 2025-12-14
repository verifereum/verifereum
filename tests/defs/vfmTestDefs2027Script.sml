open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2027";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shl_-1_1.json";
val defs = mapi (define_test "2027") tests;
val () = export_theory_no_docs ();
