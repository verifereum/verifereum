Theory vfmTestDefs1421[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stDelegatecallTestHomestead/callcode_lose_gas_oog/callcode_lose_gas_oog.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stDelegatecallTestHomestead/callcode_lose_gas_oog/callcode_lose_gas_oog.json");
val defs = mapi (define_test "1421") tests;
