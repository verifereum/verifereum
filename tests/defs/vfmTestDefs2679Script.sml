open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2679";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/pointAdd.json";
val defs = mapi (define_test "2679") tests;
val () = export_theory_no_docs ();
