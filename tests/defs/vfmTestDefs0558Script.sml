open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0558";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcode_01_OOGE.json";
val defs = mapi (define_test "0558") tests;
val () = export_theory_no_docs ();
