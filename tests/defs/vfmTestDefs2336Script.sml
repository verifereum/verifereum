Theory vfmTestDefs2336[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip7002_el_triggerable_withdrawals/withdrawal_requests/withdrawal_requests.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip7002_el_triggerable_withdrawals/withdrawal_requests/withdrawal_requests.json");
val defs = mapi (define_test "2336") tests;
