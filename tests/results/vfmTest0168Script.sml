open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0168Theory;
val () = new_theory "vfmTest0168";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0168") $ get_result_defs "vfmTestDefs0168";
val () = export_theory_no_docs ();
