Theory vfmTestDefs0113[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/cancun/eip7516_blobgasfee/test_blobbasefee_out_of_gas.json";
val defs = mapi (define_test "0113") tests;
