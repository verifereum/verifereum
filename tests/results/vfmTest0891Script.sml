open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0891Theory;
val () = new_theory "vfmTest0891";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0891") $ get_result_defs "vfmTestDefs0891";
val () = export_theory_no_docs ();
