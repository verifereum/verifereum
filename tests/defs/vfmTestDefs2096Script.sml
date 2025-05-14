open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2096";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/sar_2^256-1_1.json";
val defs = mapi (define_test "2096") tests;
val () = export_theory_no_docs ();
