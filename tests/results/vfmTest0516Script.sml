open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0516Theory;
val () = new_theory "vfmTest0516";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0516") $ get_result_defs "vfmTestDefs0516";
val () = export_theory_no_docs ();
