open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0597";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcodecall_10_SuicideEnd.json";
val defs = mapi (define_test "0597") tests;
val () = export_theory_no_docs ();
