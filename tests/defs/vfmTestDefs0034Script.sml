Theory vfmTestDefs0034[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/byzantium/eip214_staticcall/staticcall/staticcall_call_to_precompile_from_contract_init.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/byzantium/eip214_staticcall/staticcall/staticcall_call_to_precompile_from_contract_init.json");
val defs = mapi (define_test "0034") tests;
