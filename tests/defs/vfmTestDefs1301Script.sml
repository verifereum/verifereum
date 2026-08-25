Theory vfmTestDefs1301[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecoverUnrecoverableKey.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecoverUnrecoverableKey.json");
val defs = mapi (define_test "1301") tests;
