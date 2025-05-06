open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0861Theory;
val () = new_theory "vfmTest0861";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0861") $ get_result_defs "vfmTestDefs0861";
val () = export_theory_no_docs ();
