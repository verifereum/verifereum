open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0174";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip2537_bls_12_381_precompiles/bls12_variable_length_input_contracts/invalid_length_pairing.json";
val defs = mapi (define_test "0174") tests;
val () = export_theory_no_docs ();
