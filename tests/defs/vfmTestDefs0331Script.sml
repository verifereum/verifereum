Theory vfmTestDefs0331[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/amsterdam/eip7954_increase_max_contract_size/eip_mainnet/code_size_limit_mainnet.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/amsterdam/eip7954_increase_max_contract_size/eip_mainnet/code_size_limit_mainnet.json");
val defs = mapi (define_test "0331") tests;
