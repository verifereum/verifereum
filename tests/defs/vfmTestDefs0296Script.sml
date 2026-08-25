Theory vfmTestDefs0296[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip7685_general_purpose_el_requests/test_invalid_multi_type_requests.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip7685_general_purpose_el_requests/test_invalid_multi_type_requests.json");
val defs = mapi (define_test "0296") tests;
