Theory vfmTest0587[no_sig_docs]
Ancestors vfmTestDefs0587
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0587_0.nsv"];
val thyn = "vfmTestDefs0587";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
