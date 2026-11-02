Theory vfmTestDefs2735[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stStaticCall/staticcall_to_precompile_from_transaction/staticcall_to_precompile_from_transaction.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stStaticCall/staticcall_to_precompile_from_transaction/staticcall_to_precompile_from_transaction.json");
val defs = mapi (define_test "2735") tests;
