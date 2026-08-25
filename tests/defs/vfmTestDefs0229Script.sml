Theory vfmTestDefs0229[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/osaka/eip7951_p256verify_precompiles/test_precompile_will_return_success_with_tx_value.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/osaka/eip7951_p256verify_precompiles/test_precompile_will_return_success_with_tx_value.json");
val defs = mapi (define_test "0229") tests;
