open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2065";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSpecialTest/deploymentError.json";
val defs = mapi (define_test "2065") tests;
val () = export_theory_no_docs ();
