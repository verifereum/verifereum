Theory vfmTestDefs0412[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/Cancun/stEIP4844_blobtransactions/wrongBlobhashVersion.json";
val defs = mapi (define_test "0412") tests;
