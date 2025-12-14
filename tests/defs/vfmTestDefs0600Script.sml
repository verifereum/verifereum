open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0600";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcodecallcode_11_OOGE.json";
val defs = mapi (define_test "0600") tests;
val () = export_theory_no_docs ();
