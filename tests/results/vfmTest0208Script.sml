open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0208Theory;
val () = new_theory "vfmTest0208";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0208") $ get_result_defs "vfmTestDefs0208";
val () = export_theory_no_docs ();
