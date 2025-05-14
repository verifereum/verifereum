open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0128";
val tests = json_path_to_tests "../fixtures/blockchain_tests/istanbul/eip152_blake2/blake2/blake2b_gas_limit.json";
val defs = mapi (define_test "0128") tests;
val () = export_theory_no_docs ();
