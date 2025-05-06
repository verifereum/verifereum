open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0692Theory;
val () = new_theory "vfmTest0692";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0692") $ get_result_defs "vfmTestDefs0692";
val () = export_theory_no_docs ();
