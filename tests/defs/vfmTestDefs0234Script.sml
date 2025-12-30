Theory vfmTestDefs0234[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/paris/eip7610_create_collision/test_init_collision_create_opcode.json";
val defs = mapi (define_test "0234") tests;
