open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0486";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcodeDynamicCode.json";
val defs = mapi (define_test "0486") tests;
val () = export_theory_no_docs ();
