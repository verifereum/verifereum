open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0681Theory;
val () = new_theory "vfmTest0681";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0681") $ get_result_defs "vfmTestDefs0681";
val () = export_theory_no_docs ();
