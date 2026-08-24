Theory vfmTest0021[no_sig_docs]
Ancestors vfmTestDefs0021
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0021_0.nsv"];
val thyn = "vfmTestDefs0021";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
