Theory vfmTestDefs0422[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/Shanghai/stEIP3860_limitmeterinitcode/create2InitCodeSizeLimit.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/Shanghai/stEIP3860_limitmeterinitcode/create2InitCodeSizeLimit.json");
val defs = mapi (define_test "0422") tests;
