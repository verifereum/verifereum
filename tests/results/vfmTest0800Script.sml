open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0800Theory;
val () = new_theory "vfmTest0800";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0800") $ get_result_defs "vfmTestDefs0800";
val () = export_theory_no_docs ();
