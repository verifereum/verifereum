open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0385";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip3855_push0/test_push0_contracts.json";
val defs = mapi (define_test "0385") tests;
val () = export_theory_no_docs ();
