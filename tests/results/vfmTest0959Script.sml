Theory vfmTest0959[no_sig_docs]
Ancestors vfmTestDefs0959
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0959_0.nsv"];
val thyn = "vfmTestDefs0959";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
