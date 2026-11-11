Theory vfmTestDefs2213[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip7685_general_purpose_el_requests/multi_type_requests/withdrawals_credited_before_request_system_call.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip7685_general_purpose_el_requests/multi_type_requests/withdrawals_credited_before_request_system_call.json");
val defs = mapi (define_test "2213") tests;
