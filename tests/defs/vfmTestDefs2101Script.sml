Theory vfmTestDefs2101[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_Call1024BalanceTooLow.json";
val defs = mapi (define_test "2101") tests;
