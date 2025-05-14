open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2416";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecallcodecall_110_OOGE2.json";
val defs = mapi (define_test "2416") tests;
val () = export_theory_no_docs ();
