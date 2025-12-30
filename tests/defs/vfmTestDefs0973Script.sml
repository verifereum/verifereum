Theory vfmTestDefs0973[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP158Specific/EXTCODESIZE_toEpmtyParis.json";
val defs = mapi (define_test "0973") tests;
