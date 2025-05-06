open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0839Theory;
val () = new_theory "vfmTest0839";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0839") $ get_result_defs "vfmTestDefs0839";
val () = export_theory_no_docs ();
