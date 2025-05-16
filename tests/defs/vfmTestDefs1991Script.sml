open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1991";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shl_-1_255.json";
val defs = mapi (define_test "1991") tests;
val () = export_theory_no_docs ();
