open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0350Theory;
val () = new_theory "vfmTest0350";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0350") $ get_result_defs "vfmTestDefs0350";
val () = export_theory_no_docs ();
