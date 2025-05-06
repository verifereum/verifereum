open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0250Theory;
val () = new_theory "vfmTest0250";
val thyn = "vfmTestDefs0250";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
