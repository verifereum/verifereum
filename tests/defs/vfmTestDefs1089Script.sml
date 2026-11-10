Theory vfmTestDefs1089[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/frontier/precompiles/ecrecover/repeated_underfunded_calls.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/frontier/precompiles/ecrecover/repeated_underfunded_calls.json");
val defs = mapi (define_test "1089") tests;
