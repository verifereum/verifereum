Theory vfmTest1779[no_sig_docs]
Ancestors vfmTestDefs1779
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1779_0.nsv", "result1779_1.nsv"];
val thyn = "vfmTestDefs1779";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
