open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0158";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip2537_bls_12_381_precompiles/bls12_map_fp2_to_g2/valid.json";
val defs = mapi (define_test "0158") tests;
val () = export_theory_no_docs ();
