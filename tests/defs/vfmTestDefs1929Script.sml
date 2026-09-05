Theory vfmTestDefs1929[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_callcodecallcall_100/static_callcodecallcall_100.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_callcodecallcall_100/static_callcodecallcall_100.json");
val defs = mapi (define_test "1929") tests;
