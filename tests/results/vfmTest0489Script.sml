open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0489Theory;
val () = new_theory "vfmTest0489";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0489") $ get_result_defs "vfmTestDefs0489";
val () = export_theory_no_docs ();
