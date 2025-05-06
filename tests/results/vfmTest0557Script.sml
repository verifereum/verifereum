open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0557Theory;
val () = new_theory "vfmTest0557";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0557") $ get_result_defs "vfmTestDefs0557";
val () = export_theory_no_docs ();
