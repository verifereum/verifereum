open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0467";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcallcallcode_001_SuicideMiddle.json";
val defs = mapi (define_test "0467") tests;
val () = export_theory_no_docs ();
