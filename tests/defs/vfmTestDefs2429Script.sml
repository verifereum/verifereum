open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2429";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/createNameRegistratorZeroMem.json";
val defs = mapi (define_test "2429") tests;
val () = export_theory_no_docs ();
