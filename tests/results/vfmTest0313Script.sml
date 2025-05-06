open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0313Theory;
val () = new_theory "vfmTest0313";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0313") $ get_result_defs "vfmTestDefs0313";
val () = export_theory_no_docs ();
