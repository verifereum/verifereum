Theory vfmTestDefs0869[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stMemoryStressTest/delegatecall_bounds/delegatecall_bounds.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stMemoryStressTest/delegatecall_bounds/delegatecall_bounds.json");
val defs = mapi (define_test "0869") tests;
