open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0508Theory;
val () = new_theory "vfmTest0508";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0508") $ get_result_defs "vfmTestDefs0508";
val () = export_theory_no_docs ();
