open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs057";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip7516_blobgasfee/blobgasfee_opcode/blobbasefee_before_fork.json";
val defs = mapi (define_state_test "057") tests;
val () = export_theory_no_docs ();
