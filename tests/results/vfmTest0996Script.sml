open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0996Theory;
val () = new_theory "vfmTest0996";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0996") $ get_result_defs "vfmTestDefs0996";
val () = export_theory_no_docs ();
