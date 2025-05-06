open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0659Theory;
val () = new_theory "vfmTest0659";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0659") $ get_result_defs "vfmTestDefs0659";
val () = export_theory_no_docs ();
