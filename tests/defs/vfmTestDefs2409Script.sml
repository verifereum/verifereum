Theory vfmTestDefs2409[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stSelfBalance/self_balance_call_types/self_balance_call_types.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stSelfBalance/self_balance_call_types/self_balance_call_types.json");
val defs = mapi (define_test "2409") tests;
