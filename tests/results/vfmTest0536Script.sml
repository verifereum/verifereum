open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0536Theory;
val () = new_theory "vfmTest0536";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0536") $ get_result_defs "vfmTestDefs0536";
val () = export_theory_no_docs ();
