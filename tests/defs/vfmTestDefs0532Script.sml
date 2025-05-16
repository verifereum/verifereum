open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0532";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/CallRecursiveBombPreCall.json";
val defs = mapi (define_test "0532") tests;
val () = export_theory_no_docs ();
