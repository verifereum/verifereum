open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2650";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecpairing_bad_length_193.json";
val defs = mapi (define_test "2650") tests;
val () = export_theory_no_docs ();
