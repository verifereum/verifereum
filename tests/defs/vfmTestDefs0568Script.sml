open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0568";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcodecallcode_011_OOGE.json";
val defs = mapi (define_test "0568") tests;
val () = export_theory_no_docs ();
