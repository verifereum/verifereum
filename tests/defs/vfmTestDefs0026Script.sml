Theory vfmTestDefs0026[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip1153_tstore/test_transient_storage_unset_values.json";
val defs = mapi (define_test "0026") tests;
