Theory vfmTestDefs0390[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7981_increase_access_list_cost/transaction_validity/mixed_zero_nonzero_bytes_floor_cost.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7981_increase_access_list_cost/transaction_validity/mixed_zero_nonzero_bytes_floor_cost.json");
val defs = mapi (define_test "0390") tests;
