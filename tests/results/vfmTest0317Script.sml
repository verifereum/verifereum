open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0317Theory;
val () = new_theory "vfmTest0317";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0317") $ get_result_defs "vfmTestDefs0317";
val () = export_theory_no_docs ();
