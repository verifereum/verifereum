open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0137";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip2537_bls_12_381_precompiles/bls12_g1msm/call_types.json";
val defs = mapi (define_test "0137") tests;
val () = export_theory_no_docs ();
