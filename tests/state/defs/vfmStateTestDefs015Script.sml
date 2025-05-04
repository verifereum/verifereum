open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs015";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/tstorage_create_contexts/contract_creation.json";
val defs = mapi (define_state_test "015") tests;
val () = export_theory_no_docs ();
