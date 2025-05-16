open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2038";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStackTests/stackOverflow.json";
val defs = mapi (define_test "2038") tests;
val () = export_theory_no_docs ();
