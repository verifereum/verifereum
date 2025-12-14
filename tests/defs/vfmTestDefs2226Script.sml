open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2226";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_call_value_inherit_from_call.json";
val defs = mapi (define_test "2226") tests;
val () = export_theory_no_docs ();
