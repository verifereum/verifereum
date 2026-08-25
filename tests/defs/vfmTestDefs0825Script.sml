Theory vfmTestDefs0825[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stCreate2/create2collisionSelfdestructedOOG.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stCreate2/create2collisionSelfdestructedOOG.json");
val defs = mapi (define_test "0825") tests;
