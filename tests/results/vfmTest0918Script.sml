Theory vfmTest0918[no_sig_docs]
Ancestors vfmTestDefs0918
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0918_0.nsv"];
val thyn = "vfmTestDefs0918";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
