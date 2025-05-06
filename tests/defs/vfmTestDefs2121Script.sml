open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2121";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSolidityTest/CallInfiniteLoop.json";
val defs = mapi (define_test "2121") tests;
val () = export_theory_no_docs ();
