open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2364";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/CallToNameRegistratorNotMuchMemory0.json";
val defs = mapi (define_test "2364") tests;
val () = export_theory_no_docs ();
