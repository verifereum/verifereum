Theory vfmTestDefs0991[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/cancun/eip6780_selfdestruct/selfdestruct/calling_from_new_contract_to_pre_existing_contract.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/cancun/eip6780_selfdestruct/selfdestruct/calling_from_new_contract_to_pre_existing_contract.json");
val defs = mapi (define_test "0991") tests;
