Theory vfmTestDefs2302[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecallcall_100_OOGE2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stStaticCall/static_callcodecallcall_100_OOGE2.json");
val defs = mapi (define_test "2302") tests;
