open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1107";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stLogTests/log2_Caller.json";
val defs = mapi (define_test "1107") tests;
val () = export_theory_no_docs ();
