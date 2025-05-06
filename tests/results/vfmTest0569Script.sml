open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0569Theory;
val () = new_theory "vfmTest0569";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0569") $ get_result_defs "vfmTestDefs0569";
val () = export_theory_no_docs ();
