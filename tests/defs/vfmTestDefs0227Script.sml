Theory vfmTestDefs0227[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/osaka/eip7951_p256verify_precompiles/test_precompile_as_tx_entry_point.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/osaka/eip7951_p256verify_precompiles/test_precompile_as_tx_entry_point.json");
val defs = mapi (define_test "0227") tests;
