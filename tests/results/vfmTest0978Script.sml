open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0978Theory;
val () = new_theory "vfmTest0978";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0978") $ get_result_defs "vfmTestDefs0978";
val () = export_theory_no_docs ();
