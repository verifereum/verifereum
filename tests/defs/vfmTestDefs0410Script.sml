Theory vfmTestDefs0410[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7997_deterministic_factory_contract/factory/factory_short_calldata_out_of_gas.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7997_deterministic_factory_contract/factory/factory_short_calldata_out_of_gas.json");
val defs = mapi (define_test "0410") tests;
