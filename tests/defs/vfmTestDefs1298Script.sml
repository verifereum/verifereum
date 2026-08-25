Theory vfmTestDefs1298[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecoverInvalidSignature.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stPreCompiledContracts2/CallEcrecoverInvalidSignature.json");
val defs = mapi (define_test "1298") tests;
