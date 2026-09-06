Theory vfmTestDefs0204[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/frontier/opcodes/dynamic_jump/jumpi_not_taken_invalid_destination.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/frontier/opcodes/dynamic_jump/jumpi_not_taken_invalid_destination.json");
val defs = mapi (define_test "0204") tests;
