open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0399Theory;
val () = new_theory "vfmTest0399";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0399") $ get_result_defs "vfmTestDefs0399";
val () = export_theory_no_docs ();
