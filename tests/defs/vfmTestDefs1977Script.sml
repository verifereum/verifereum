open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1977";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/sar_2^256-1_0.json";
val defs = mapi (define_test "1977") tests;
val () = export_theory_no_docs ();
