open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs072";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/istanbul/eip1344_chainid/chainid/chainid.json";
val defs = mapi (define_state_test "072") tests;
val () = export_theory_no_docs ();
