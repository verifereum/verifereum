Theory vfmTestDefs0367[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7976_increase_calldata_floor_cost/refunds/gas_refunds_from_data_floor.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7976_increase_calldata_floor_cost/refunds/gas_refunds_from_data_floor.json");
val defs = mapi (define_test "0367") tests;
