Theory vfmTest0406[no_sig_docs]
Ancestors vfmTestDefs0406
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0406_0.nsv"];
val thyn = "vfmTestDefs0406";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
