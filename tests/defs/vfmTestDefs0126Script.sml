open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0126";
val tests = json_path_to_tests "../fixtures/blockchain_tests/istanbul/eip152_blake2/blake2/blake2b_large_gas_limit.json";
val defs = mapi (define_test "0126") tests;
val () = export_theory_no_docs ();
