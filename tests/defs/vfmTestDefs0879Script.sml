Theory vfmTestDefs0879[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/berlin/eip2930_access_list/tx_intrinsic_gas/tx_intrinsic_gas.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/berlin/eip2930_access_list/tx_intrinsic_gas/tx_intrinsic_gas.json");
val defs = mapi (define_test "0879") tests;
