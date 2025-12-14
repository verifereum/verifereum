open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0387";
val tests = json_path_to_tests "../fixtures/blockchain_tests/shanghai/eip3860_initcode/test_create_opcode_initcode.json";
val defs = mapi (define_test "0387") tests;
val () = export_theory_no_docs ();
