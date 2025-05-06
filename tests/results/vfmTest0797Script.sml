open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0797Theory;
val () = new_theory "vfmTest0797";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0797") $ get_result_defs "vfmTestDefs0797";
val () = export_theory_no_docs ();
