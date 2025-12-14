open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0160";
val tests = json_path_to_tests "../fixtures/blockchain_tests/istanbul/eip152_blake2/test_blake2b_gas_limit.json";
val defs = mapi (define_test "0160") tests;
val () = export_theory_no_docs ();
