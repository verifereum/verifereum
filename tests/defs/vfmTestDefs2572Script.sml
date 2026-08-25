Theory vfmTestDefs2572[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stZeroCallsTest/ZeroValue_SUICIDE.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stZeroCallsTest/ZeroValue_SUICIDE.json");
val defs = mapi (define_test "2572") tests;
