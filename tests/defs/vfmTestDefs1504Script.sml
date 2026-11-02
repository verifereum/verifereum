Theory vfmTestDefs1504[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stEIP4844_blobtransactions/opcode_blobh_bounds/opcode_blobh_bounds.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stEIP4844_blobtransactions/opcode_blobh_bounds/opcode_blobh_bounds.json");
val defs = mapi (define_test "1504") tests;
