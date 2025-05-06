open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1659Theory;
val () = new_theory "vfmTest1659";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1659") $ get_result_defs "vfmTestDefs1659";
val () = export_theory_no_docs ();
