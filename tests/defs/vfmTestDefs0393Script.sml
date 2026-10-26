Theory vfmTestDefs0393[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7997_deterministic_factory_contract/eip_mainnet/eip_7997.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7997_deterministic_factory_contract/eip_mainnet/eip_7997.json");
val defs = mapi (define_test "0393") tests;
