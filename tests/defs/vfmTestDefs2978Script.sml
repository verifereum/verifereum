Theory vfmTestDefs2978[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/prague/eip2537_bls_12_381_precompiles/bls12_g1add/invalid.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/prague/eip2537_bls_12_381_precompiles/bls12_g1add/invalid.json");
val defs = mapi (define_test "2978") tests;
