open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0496Theory;
val () = new_theory "vfmTest0496";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0496") $ get_result_defs "vfmTestDefs0496";
val () = export_theory_no_docs ();
