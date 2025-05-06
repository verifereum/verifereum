open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0155";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip2537_bls_12_381_precompiles/bls12_map_fp_to_g1/call_types.json";
val defs = mapi (define_test "0155") tests;
val () = export_theory_no_docs ();
