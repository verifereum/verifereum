open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs206";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/byzantium/eip198_modexp_precompile/modexp/modexp.json";
val defs = mapi (define_state_test "206") tests;
val () = export_theory_no_docs ();
