open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0966";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stInitCodeTest/CallRecursiveContract.json";
val defs = mapi (define_test "0966") tests;
val () = export_theory_no_docs ();
