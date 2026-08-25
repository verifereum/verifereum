Theory vfmTestDefs0005[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/berlin/eip2930_access_list/test_transaction_intrinsic_gas_cost.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/berlin/eip2930_access_list/test_transaction_intrinsic_gas_cost.json");
val defs = mapi (define_test "0005") tests;
