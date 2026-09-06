Theory vfmTestDefs0979[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stPreCompiledContracts/precomps_eip2929_cancun/precomps_eip2929_cancun.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stPreCompiledContracts/precomps_eip2929_cancun/precomps_eip2929_cancun.json");
val defs = mapi (define_test "0979") tests;
