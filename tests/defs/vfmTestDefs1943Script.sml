Theory vfmTestDefs1943[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_callcodecallcall_abcb_recursive/static_callcodecallcall_abcb_recursive.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_callcodecallcall_abcb_recursive/static_callcodecallcall_abcb_recursive.json");
val defs = mapi (define_test "1943") tests;
