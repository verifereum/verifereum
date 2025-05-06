open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0199Theory;
val () = new_theory "vfmTest0199";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0199") $ get_result_defs "vfmTestDefs0199";
val () = export_theory_no_docs ();
