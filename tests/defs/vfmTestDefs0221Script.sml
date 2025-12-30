Theory vfmTestDefs0221[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7951_p256verify_precompiles/test_call_types.json";
val defs = mapi (define_test "0221") tests;
