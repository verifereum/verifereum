open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2199";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcallcall_000_OOGMBefore.json";
val defs = mapi (define_test "2199") tests;
val () = export_theory_no_docs ();
