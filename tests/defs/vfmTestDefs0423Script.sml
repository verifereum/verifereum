Theory vfmTestDefs0423[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/Shanghai/stEIP3860_limitmeterinitcode/createInitCodeSizeLimit.json";
val defs = mapi (define_test "0423") tests;
