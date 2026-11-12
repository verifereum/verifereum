Theory vfmTest0262[no_sig_docs]
Ancestors vfmTestDefs0262
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0262_0.nsv"];
val thyn = "vfmTestDefs0262";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
