Theory vfmTestDefs2271[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip2537_bls_12_381_precompiles/bls12_g1add/gas.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip2537_bls_12_381_precompiles/bls12_g1add/gas.json");
val defs = mapi (define_test "2271") tests;
