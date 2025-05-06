open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0753Theory;
val () = new_theory "vfmTest0753";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0753") $ get_result_defs "vfmTestDefs0753";
val () = export_theory_no_docs ();
