open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0825Theory;
val () = new_theory "vfmTest0825";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0825") $ get_result_defs "vfmTestDefs0825";
val () = export_theory_no_docs ();
