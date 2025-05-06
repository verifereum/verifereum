open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2080";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/sar11.json";
val defs = mapi (define_test "2080") tests;
val () = export_theory_no_docs ();
