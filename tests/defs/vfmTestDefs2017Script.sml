open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2017";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/sar_2^256-1_255.json";
val defs = mapi (define_test "2017") tests;
val () = export_theory_no_docs ();
