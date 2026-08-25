Theory vfmTestDefs2308[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecallcall_100_OOGMBefore2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stStaticCall/static_callcodecallcall_100_OOGMBefore2.json");
val defs = mapi (define_test "2308") tests;
