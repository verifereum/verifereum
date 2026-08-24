Theory vfmTest0755[no_sig_docs]
Ancestors vfmTestDefs0755
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0755_0.nsv"];
val thyn = "vfmTestDefs0755";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
