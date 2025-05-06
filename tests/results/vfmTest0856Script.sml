open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0856Theory;
val () = new_theory "vfmTest0856";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0856") $ get_result_defs "vfmTestDefs0856";
val () = export_theory_no_docs ();
