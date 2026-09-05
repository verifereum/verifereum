Theory vfmTestDefs2334[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip7002_el_triggerable_withdrawals/modified_withdrawal_contract/extra_withdrawals.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip7002_el_triggerable_withdrawals/modified_withdrawal_contract/extra_withdrawals.json");
val defs = mapi (define_test "2334") tests;
