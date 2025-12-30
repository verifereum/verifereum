Theory vfmTestDefs0228[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/osaka/eip7951_p256verify_precompiles/test_precompile_before_fork.json";
val defs = mapi (define_test "0228") tests;
