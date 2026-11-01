Theory vfmTestDefs0363[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7976_increase_calldata_floor_cost/execution_gas/full_gas_consumption.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7976_increase_calldata_floor_cost/execution_gas/full_gas_consumption.json");
val defs = mapi (define_test "0363") tests;
