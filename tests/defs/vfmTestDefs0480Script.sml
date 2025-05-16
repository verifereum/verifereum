open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0480";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcodecallcode_011_OOGE.json";
val defs = mapi (define_test "0480") tests;
val () = export_theory_no_docs ();
