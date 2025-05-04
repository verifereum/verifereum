open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs009";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/tstorage/gas_usage.json";
val defs = mapi (define_state_test "009") tests;
val () = export_theory_no_docs ();
