open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0477Theory;
val () = new_theory "vfmTest0477";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0477") $ get_result_defs "vfmTestDefs0477";
val () = export_theory_no_docs ();
