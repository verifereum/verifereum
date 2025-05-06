open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2094";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/sar_2^256-1_256.json";
val defs = mapi (define_test "2094") tests;
val () = export_theory_no_docs ();
