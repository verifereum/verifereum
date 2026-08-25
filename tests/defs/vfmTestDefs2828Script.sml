Theory vfmTestDefs2828[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_0-3_9935_28000_128.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_0-3_9935_28000_128.json");
val defs = mapi (define_test "2828") tests;
