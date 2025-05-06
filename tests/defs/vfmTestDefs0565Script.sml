open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0565";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcall_00_OOGE.json";
val defs = mapi (define_test "0565") tests;
val () = export_theory_no_docs ();
