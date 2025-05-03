open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs149";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/tstorage_create_contexts/contract_creation.json";
val defs = mapi (define_state_test "149") tests;
val () = export_theory_no_docs ();
