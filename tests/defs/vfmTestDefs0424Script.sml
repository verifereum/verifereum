Theory vfmTestDefs0424[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/Shanghai/stEIP3860_limitmeterinitcode/creationTxInitCodeSizeLimit.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/Shanghai/stEIP3860_limitmeterinitcode/creationTxInitCodeSizeLimit.json");
val defs = mapi (define_test "0424") tests;
