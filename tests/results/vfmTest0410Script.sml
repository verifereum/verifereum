open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0410Theory;
val () = new_theory "vfmTest0410";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0410") $ get_result_defs "vfmTestDefs0410";
val () = export_theory_no_docs ();
