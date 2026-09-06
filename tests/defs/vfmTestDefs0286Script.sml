Theory vfmTestDefs0286[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/osaka/eip7951_p256verify_precompiles/eip_mainnet/invalid.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/osaka/eip7951_p256verify_precompiles/eip_mainnet/invalid.json");
val defs = mapi (define_test "0286") tests;
