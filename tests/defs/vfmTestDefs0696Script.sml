Theory vfmTestDefs0696[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stDelegatecallTestHomestead/delegatecode_dynamic_code2_self_call/delegatecode_dynamic_code2_self_call.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stDelegatecallTestHomestead/delegatecode_dynamic_code2_self_call/delegatecode_dynamic_code2_self_call.json");
val defs = mapi (define_test "0696") tests;
