open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0539";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCodes/callcall_00.json";
val defs = mapi (define_test "0539") tests;
val () = export_theory_no_docs ();
