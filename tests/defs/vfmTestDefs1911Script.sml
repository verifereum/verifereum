Theory vfmTestDefs1911[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatasize_after_failing_delegatecall.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stReturnDataTest/returndatasize_after_failing_delegatecall.json");
val defs = mapi (define_test "1911") tests;
