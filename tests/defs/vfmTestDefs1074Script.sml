Theory vfmTestDefs1074[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/frontier/opcodes/calldataload/calldataload.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/frontier/opcodes/calldataload/calldataload.json");
val defs = mapi (define_test "1074") tests;
