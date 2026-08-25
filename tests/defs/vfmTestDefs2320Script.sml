Theory vfmTestDefs2320[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcodecallcallcode_101_OOGMAfter2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stStaticCall/static_callcodecallcallcode_101_OOGMAfter2.json");
val defs = mapi (define_test "2320") tests;
