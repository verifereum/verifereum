Theory vfmTestDefs0640[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreate2/revert_opcode_in_create_returns_create2/revert_opcode_in_create_returns_create2.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreate2/revert_opcode_in_create_returns_create2/revert_opcode_in_create_returns_create2.json");
val defs = mapi (define_test "0640") tests;
