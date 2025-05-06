open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0451Theory;
val () = new_theory "vfmTest0451";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0451") $ get_result_defs "vfmTestDefs0451";
val () = export_theory_no_docs ();
