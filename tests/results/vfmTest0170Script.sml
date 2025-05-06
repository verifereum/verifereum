open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0170Theory;
val () = new_theory "vfmTest0170";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0170") $ get_result_defs "vfmTestDefs0170";
val () = export_theory_no_docs ();
