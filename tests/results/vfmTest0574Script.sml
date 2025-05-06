open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0574Theory;
val () = new_theory "vfmTest0574";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0574") $ get_result_defs "vfmTestDefs0574";
val () = export_theory_no_docs ();
