open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs000";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/shanghai/eip3651_warm_coinbase/warm_coinbase/warm_coinbase_call_out_of_gas.json";
val defs = mapi (define_state_test "000") tests;
val () = export_theory_no_docs ();
