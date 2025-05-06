open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0535Theory;
val () = new_theory "vfmTest0535";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0535") $ get_result_defs "vfmTestDefs0535";
val () = export_theory_no_docs ();
