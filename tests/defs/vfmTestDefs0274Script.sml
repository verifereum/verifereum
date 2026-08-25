Theory vfmTestDefs0274[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/prague/eip7002_el_triggerable_withdrawals/test_eip_7002.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/prague/eip7002_el_triggerable_withdrawals/test_eip_7002.json");
val defs = mapi (define_test "0274") tests;
