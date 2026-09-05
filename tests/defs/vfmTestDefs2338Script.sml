Theory vfmTestDefs2338[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip7002_el_triggerable_withdrawals/withdrawal_requests_out_of_gas/withdrawal_requests_out_of_gas.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip7002_el_triggerable_withdrawals/withdrawal_requests_out_of_gas/withdrawal_requests_out_of_gas.json");
val defs = mapi (define_test "2338") tests;
