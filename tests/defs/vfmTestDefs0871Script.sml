Theory vfmTestDefs0871[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stMemoryStressTest/delegatecall_bounds3/delegatecall_bounds3.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stMemoryStressTest/delegatecall_bounds3/delegatecall_bounds3.json");
val defs = mapi (define_test "0871") tests;
