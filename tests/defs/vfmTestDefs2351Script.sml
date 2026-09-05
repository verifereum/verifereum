Theory vfmTestDefs2351[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip7685_general_purpose_el_requests/multi_type_requests/invalid_multi_type_requests.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip7685_general_purpose_el_requests/multi_type_requests/invalid_multi_type_requests.json");
val defs = mapi (define_test "2351") tests;
