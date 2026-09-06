Theory vfmTestDefs0857[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stMemExpandingEIP150Calls/oo_gin_return/oo_gin_return.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stMemExpandingEIP150Calls/oo_gin_return/oo_gin_return.json");
val defs = mapi (define_test "0857") tests;
