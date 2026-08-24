Theory vfmTest0741[no_sig_docs]
Ancestors vfmTestDefs0741
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0741_0.nsv"];
val thyn = "vfmTestDefs0741";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
