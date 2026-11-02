Theory vfmTestDefs3005[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/prague/eip2537_bls_12_381_precompiles/bls12_map_fp_to_g1/isogeny_kernel_values.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/prague/eip2537_bls_12_381_precompiles/bls12_map_fp_to_g1/isogeny_kernel_values.json");
val defs = mapi (define_test "3005") tests;
