open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs170";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip7516_blobgasfee/blobgasfee_opcode/blobbasefee_out_of_gas.json";
val defs = mapi (define_state_test "170") tests;
val () = export_theory_no_docs ();
