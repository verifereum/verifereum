open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0678Theory;
val () = new_theory "vfmTest0678";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0678") $ get_result_defs "vfmTestDefs0678";
val () = export_theory_no_docs ();
