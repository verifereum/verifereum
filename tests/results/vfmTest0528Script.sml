open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0528Theory;
val () = new_theory "vfmTest0528";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0528") $ get_result_defs "vfmTestDefs0528";
val () = export_theory_no_docs ();
