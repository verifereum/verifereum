Theory vfmTestDefs0418[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/Shanghai/stEIP3651_warmcoinbase/coinbaseWarmAccountCallGasFail.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/Shanghai/stEIP3651_warmcoinbase/coinbaseWarmAccountCallGasFail.json");
val defs = mapi (define_test "0418") tests;
