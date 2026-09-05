Theory vfmTestDefs2024[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stStaticCall/static_revert_opcode_calls/static_revert_opcode_calls.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stStaticCall/static_revert_opcode_calls/static_revert_opcode_calls.json");
val defs = mapi (define_test "2024") tests;
