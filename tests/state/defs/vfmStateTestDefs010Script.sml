open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs010";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip1153_tstore/tstorage/run_until_out_of_gas.json";
val defs = mapi (define_state_test "010") tests;
val () = export_theory_no_docs ();
