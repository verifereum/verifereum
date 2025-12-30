Theory vfmTestDefs0966[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP1559/tipTooHigh.json";
val defs = mapi (define_test "0966") tests;
