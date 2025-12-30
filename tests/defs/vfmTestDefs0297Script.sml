Theory vfmTestDefs0297[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7685_general_purpose_el_requests/test_valid_multi_type_request_from_same_tx.json";
val defs = mapi (define_test "0297") tests;
