Theory vfmTestDefs0420[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/Shanghai/stEIP3855_push0/push0Gas.json";
val defs = mapi (define_test "0420") tests;
