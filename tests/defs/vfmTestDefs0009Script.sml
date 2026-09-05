Theory vfmTestDefs0009[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/berlin/eip2930_access_list/acl/transaction_intrinsic_gas_cost.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/berlin/eip2930_access_list/acl/transaction_intrinsic_gas_cost.json");
val defs = mapi (define_test "0009") tests;
