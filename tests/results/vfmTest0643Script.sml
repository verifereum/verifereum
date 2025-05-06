open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0643Theory;
val () = new_theory "vfmTest0643";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0643") $ get_result_defs "vfmTestDefs0643";
val () = export_theory_no_docs ();
