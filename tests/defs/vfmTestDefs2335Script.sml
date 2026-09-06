Theory vfmTestDefs2335[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip7002_el_triggerable_withdrawals/modified_withdrawal_contract/system_contract_errors.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip7002_el_triggerable_withdrawals/modified_withdrawal_contract/system_contract_errors.json");
val defs = mapi (define_test "2335") tests;
