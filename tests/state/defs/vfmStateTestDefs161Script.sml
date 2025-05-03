open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs161";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/tstorage/run_until_out_of_gas.json";
val defs = mapi (define_state_test "161") tests;
val () = export_theory_no_docs ();
