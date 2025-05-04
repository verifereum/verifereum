open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs065";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/frontier/opcodes/dup/dup.json";
val defs = mapi (define_state_test "065") tests;
val () = export_theory_no_docs ();
