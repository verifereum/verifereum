open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2088";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/sar_2^255-1_254.json";
val defs = mapi (define_test "2088") tests;
val () = export_theory_no_docs ();
