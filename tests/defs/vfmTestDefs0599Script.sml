open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0599";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallDelegateCodesCallCodeHomestead/callcodecallcall_100_OOGE.json";
val defs = mapi (define_test "0599") tests;
val () = export_theory_no_docs ();
