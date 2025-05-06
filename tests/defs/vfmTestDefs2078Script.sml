open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2078";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/sar01.json";
val defs = mapi (define_test "2078") tests;
val () = export_theory_no_docs ();
