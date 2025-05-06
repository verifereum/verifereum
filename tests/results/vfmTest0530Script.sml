open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0530Theory;
val () = new_theory "vfmTest0530";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0530") $ get_result_defs "vfmTestDefs0530";
val () = export_theory_no_docs ();
