open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2368";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/CallToNameRegistratorTooMuchMemory1.json";
val defs = mapi (define_test "2368") tests;
val () = export_theory_no_docs ();
