Theory vfmTestDefs2976[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/prague/eip2537_bls_12_381_precompiles/bls12_g1add/call_types.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/prague/eip2537_bls_12_381_precompiles/bls12_g1add/call_types.json");
val defs = mapi (define_test "2976") tests;
