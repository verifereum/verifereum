open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0967Theory;
val () = new_theory "vfmTest0967";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0967") $ get_result_defs "vfmTestDefs0967";
val () = export_theory_no_docs ();
