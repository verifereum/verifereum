Theory vfmTestDefs0969[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stEIP158Specific/CALL_OneVCallSuicide.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stEIP158Specific/CALL_OneVCallSuicide.json");
val defs = mapi (define_test "0969") tests;
