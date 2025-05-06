open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0314Theory;
val () = new_theory "vfmTest0314";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0314") $ get_result_defs "vfmTestDefs0314";
val () = export_theory_no_docs ();
