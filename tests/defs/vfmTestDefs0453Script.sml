open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0453";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmBitwiseLogicOperation/slt.json";
val defs = mapi (define_test "0453") tests;
val () = export_theory_no_docs ();
