Theory vfmTestDefs0221[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/osaka/eip7951_p256verify_precompiles/test_call_types.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/osaka/eip7951_p256verify_precompiles/test_call_types.json");
val defs = mapi (define_test "0221") tests;
