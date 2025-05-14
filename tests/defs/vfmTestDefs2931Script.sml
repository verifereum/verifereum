open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs2931";
val tests = json_path_to_tests "../fixtures/blockchain_tests/zkevm/worst_bytecode/worst_bytecode_single_opcode.json";
val defs = mapi (define_test "2931") tests;
val () = export_theory_no_docs ();
