open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs139";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/constantinople/eip1014_create2/create_returndata/create2_return_data.json";
val defs = mapi (define_state_test "139") tests;
val () = export_theory_no_docs ();
