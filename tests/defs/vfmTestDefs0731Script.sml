open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0731";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcodecallcode_11_SuicideEnd.json";
val defs = mapi (define_test "0731") tests;
val () = export_theory_no_docs ();
