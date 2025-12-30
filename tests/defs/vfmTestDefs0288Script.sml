Theory vfmTestDefs0288[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7623_increase_calldata_cost/test_eip_7623.json";
val defs = mapi (define_test "0288") tests;
