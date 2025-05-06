open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0262Theory;
val () = new_theory "vfmTest0262";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0262") $ get_result_defs "vfmTestDefs0262";
val () = export_theory_no_docs ();
