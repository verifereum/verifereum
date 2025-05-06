open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0131Theory;
val () = new_theory "vfmTest0131";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0131") $ get_result_defs "vfmTestDefs0131";
val () = export_theory_no_docs ();
