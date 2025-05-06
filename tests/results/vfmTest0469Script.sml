open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0469Theory;
val () = new_theory "vfmTest0469";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0469") $ get_result_defs "vfmTestDefs0469";
val () = export_theory_no_docs ();
