open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs140";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/istanbul/eip1344_chainid/chainid/chainid.json";
val defs = mapi (define_state_test "140") tests;
val () = export_theory_no_docs ();
