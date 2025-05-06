open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0925Theory;
val () = new_theory "vfmTest0925";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0925") $ get_result_defs "vfmTestDefs0925";
val () = export_theory_no_docs ();
