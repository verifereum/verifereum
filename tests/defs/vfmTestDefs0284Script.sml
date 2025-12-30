Theory vfmTestDefs0284[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7251_consolidations/test_eip_7251.json";
val defs = mapi (define_test "0284") tests;
