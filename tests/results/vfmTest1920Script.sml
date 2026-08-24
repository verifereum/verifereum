Theory vfmTest1920[no_sig_docs]
Ancestors vfmTestDefs1920
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1920_0.nsv", "result1920_1.nsv"];
val thyn = "vfmTestDefs1920";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
