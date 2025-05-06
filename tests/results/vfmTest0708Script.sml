open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0708Theory;
val () = new_theory "vfmTest0708";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0708") $ get_result_defs "vfmTestDefs0708";
val () = export_theory_no_docs ();
