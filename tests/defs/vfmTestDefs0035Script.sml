Theory vfmTestDefs0035[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/byzantium/eip214_staticcall/staticcall/staticcall_nested_call_to_precompile.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/byzantium/eip214_staticcall/staticcall/staticcall_nested_call_to_precompile.json");
val defs = mapi (define_test "0035") tests;
