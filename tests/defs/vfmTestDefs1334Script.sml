open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs1334";
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRandom/randomStatetest149.json";
val defs = mapi (define_test "1334") tests;
val () = export_theory_no_docs ();
