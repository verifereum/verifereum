Theory vfmTestDefs2033[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticFlagEnabled/delegatecall_to_precompile_from_called_contract/delegatecall_to_precompile_from_called_contract.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticFlagEnabled/delegatecall_to_precompile_from_called_contract/delegatecall_to_precompile_from_called_contract.json");
val defs = mapi (define_test "2033") tests;
