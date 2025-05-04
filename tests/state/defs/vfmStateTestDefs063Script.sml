open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs063";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/frontier/opcodes/call_and_callcode_gas_calculation/value_transfer_gas_calculation.json";
val defs = mapi (define_state_test "063") tests;
val () = export_theory_no_docs ();
