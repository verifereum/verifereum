open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0161";
val tests = json_path_to_tests "../fixtures/blockchain_tests/istanbul/eip152_blake2/test_blake2b_invalid_gas.json";
val defs = mapi (define_test "0161") tests;
val () = export_theory_no_docs ();
