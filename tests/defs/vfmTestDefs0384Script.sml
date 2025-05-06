open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0384";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/VMTests/vmTests/calldatasize.json";
val defs = mapi (define_test "0384") tests;
val () = export_theory_no_docs ();
