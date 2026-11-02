Theory vfmTestDefs0407[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7997_deterministic_factory_contract/factory/factory_initcode_size_boundary.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7997_deterministic_factory_contract/factory/factory_initcode_size_boundary.json");
val defs = mapi (define_test "0407") tests;
