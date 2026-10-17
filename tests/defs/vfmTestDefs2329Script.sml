Theory vfmTestDefs2329[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip7685_general_purpose_el_requests/multi_type_requests/system_contract_deployed_and_called_in_same_block.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip7685_general_purpose_el_requests/multi_type_requests/system_contract_deployed_and_called_in_same_block.json");
val defs = mapi (define_test "2329") tests;
