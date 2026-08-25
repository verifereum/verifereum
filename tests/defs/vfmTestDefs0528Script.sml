Theory vfmTestDefs0528[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stBadOpcode/eip2315NotRemoved.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stBadOpcode/eip2315NotRemoved.json");
val defs = mapi (define_test "0528") tests;
