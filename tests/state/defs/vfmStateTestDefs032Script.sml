open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs032";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip4844_blobs/blobhash_opcode/blobhash_gas_cost.json";
val defs = mapi (define_state_test "032") tests;
val () = export_theory_no_docs ();
