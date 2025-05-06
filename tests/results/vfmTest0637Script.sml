open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0637Theory;
val () = new_theory "vfmTest0637";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0637") $ get_result_defs "vfmTestDefs0637";
val () = export_theory_no_docs ();
