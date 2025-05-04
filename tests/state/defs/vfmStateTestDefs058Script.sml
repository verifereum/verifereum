open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs058";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip7516_blobgasfee/blobgasfee_opcode/blobbasefee_out_of_gas.json";
val defs = mapi (define_state_test "058") tests;
val () = export_theory_no_docs ();
