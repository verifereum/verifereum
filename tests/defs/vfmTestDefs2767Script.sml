open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2767";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_inputs.json";
val defs = mapi (define_test "2767") tests;
val () = export_theory_no_docs ();
